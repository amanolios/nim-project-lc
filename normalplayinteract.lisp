;$ACL2s-SMode$;ACL2s
(in-package "ACL2S")

; Represents the individual object in a heap
(defdata object nat)

; Represents a heap 
(defdata heap (listof object))

; Represents binary representation of number 
(defdata bit (oneof 0 1))
(defdata bv (listof bit))

; Converts nat -> bv
(definec ntb-helper (n :nat b :bv) :bv
  (if (zp n)
    b
    (ntb-helper (floor n 2) (cons (mod n 2) b))))

(check= (ntb-helper 0 '()) '())
(check= (ntb-helper 6 '()) '(1 1 0))
(check= (ntb-helper 10 '()) '(1 0 1 0))
(check= (ntb-helper 10 '(1)) '(1 0 1 0 1))

;; n->bt: Nat --> Bv
(definec n->bt (n :nat) :bv
  (if (== n 0)
    '(0)
    (ntb-helper n '())))

(check= (n->bt 0)  '(0))
(check= (n->bt 6)  '(1 1 0))
(check= (n->bt 10) '(1 0 1 0))
(check= (n->bt 17) '(1 0 0 0 1))

; Loops for bit -> n 
(definec forloop (bv :bv power total-sum :nat) :nat
  (match bv
    (nil total-sum)
    ((f . r)
     (if (zp f)
       (forloop r (1+ power) total-sum)
       (forloop r (1+ power) (+ total-sum (expt 2 power)))))))

(check= (forloop '(1 0 1 0) 0 0) 5)
(check= (forloop '(1 0 1) 3 2) 42)
(check= (forloop '() 4 10) 10)
(check= (forloop '(0) 4 10) 10)
(check= (forloop '(0 1 0 1) 3 2) 82)

; Bv -> nat
(definec bt->n (bin :bv) :nat
  (forloop (lrev bin) 0 0))

(check= (bt->n '(1 0 1 0)) 10)  
(check= (bt->n '(1 1 1)) 7) 
(check= (bt->n '(1 0 0)) 4) 
(check= (bt->n '(1 1 1 1 1)) 31) 
(check= (bt->n ()) 0)

; list of bv, representing the heaps
(defdata lob (listof bv))

; adds an arbitrary number of zeros to b. Used for making 2 binary numbers equal length
(definec add-zeros (b :bv n :nat) :bv
  (if (== n 0)
    b
    (add-zeros (cons 0 b) (1- n))))

(check= (add-zeros '() 0) '())
(check= (add-zeros '() 2) '(0 0))
(check= (add-zeros '(1 0) 0) '(1 0))
(check= (add-zeros '(1 0) 2) '(0 0 1 0))

; makes 2 binary numbers the same length. Used to perform the xor operation on them.
(definec make-same-len (b1 b2 :bv) :lob
  (cond ((== (len b1) (len b2)) (list b1 b2))
        ((< (len b1) (len b2)) (list (add-zeros b1 (- (len b2) (len b1))) b2))
        (t (list b1 (add-zeros b2 (- (len b1) (len b2)))))))

(check= (make-same-len '() '()) (list '() '()))
(check= (make-same-len '(1) '()) (list '(1) '(0)))
(check= (make-same-len '() '(1)) (list '(0) '(1)))
(check= (make-same-len '(1 1 0) '(0 0 0)) (list '(1 1 0) '(0 0 0)))
(check= (make-same-len '(1 1 0) '(1 0)) (list '(1 1 0) '(0 1 0)))
(check= (make-same-len '(1 0) '(1 1 0)) (list '(0 1 0) '(1 1 0)))

(definec nat-xor (b1 b2 :bit) :bit
  (if (!= b1 b2)
    1
    0))

(check= (nat-xor 0 0) 0)
(check= (nat-xor 0 1) 1)
(check= (nat-xor 1 0) 1)
(check= (nat-xor 1 1) 0)

; perform xor operation on 2 binary numbers
(definec xor-two-bin-help (b1 b2 :bv output :bv) :bv
  :skip-tests t
  :skip-admissibilityp t
  :skip-function-contractp t
  :skip-body-contractsp t
  (let* ((list-bin (make-same-len b1 b2))
         (b1-new (first list-bin))
         (b2-new (second list-bin)))
    (match b1-new
      (nil (lrev output))
      ((f . r) (match b2-new
                 ((a . b) (xor-two-bin-help r b (cons (nat-xor f a) output)))))))) 

(definec xor-two-bin (b1 b2 :bv) :bv
  (xor-two-bin-help b1 b2 '()))

(check= (xor-two-bin '() '()) '())
(check= (xor-two-bin '(1) '()) '(1))
(check= (xor-two-bin '() '(1)) '(1))
(check= (xor-two-bin '(1) '(1)) '(0))
(check= (xor-two-bin '(0) '(0)) '(0))
(check= (xor-two-bin '(1 0 1) '(1 0 0 0)) '(1 1 0 1))
(check= (xor-two-bin '(1 0 0 0) '(1 0 1)) '(1 1 0 1))

; xor list of binary to another binary rep
(definec xor-bin (bins :lob l-b :nat) :nat
  :ic (== (len bins) l-b)
  :skip-tests t
  :skip-admissibilityp t
  :skip-function-contractp t
  :skip-body-contractsp t
  (match bins 
    (nil 0)
    ((f . r) (if (== l-b 1)
                 (bt->n f)
                 (match r 
                   ((a . b) (xor-bin (cons (xor-two-bin f a) b) (1- l-b))))))))

(check= (xor-bin '() 0) 0)
(check= (xor-bin '((1 0)) 1) 2)
(check= (xor-bin '((1 0) (1 0 1)) 2) 7)
(check= (xor-bin '((1 0) (1 0 1) (1)) 3) 6)

; xor one value given with list of binary numbers
(definec xor-lob-val (bins :lob b :bv) :lob
  (match bins
    (nil nil)
    ((f . r) (cons (xor-two-bin f b) (xor-lob-val r b)))))

(check= (xor-lob-val '() '(1 0)) '())
(check= (xor-lob-val '(()) '(1 0)) '((1 0)))
(check= (xor-lob-val '((1 0) (1 0 1 1) (0)) '(1 0 0)) '((1 1 0) (1 1 1 1) (1 0 0)))

; converts heap to lob so can be properly xor'd and evaluated
(definec heap->lob (h :heap) :lob
  (match h
    (nil '())
    ((f . r) (cons (n->bt f) (heap->lob r)))))

(check= (heap->lob '()) '())
(check= (heap->lob '(1)) '((1)))
(check= (heap->lob '(1 1)) '((1) (1)))
(check= (heap->lob '(23 1 10 14)) '((1 0 1 1 1) (1) (1 0 1 0) (1 1 1 0)))

; converts lob to heap so can be properly evaluated during making an optimal move
(definec lob->heap (l :lob) :heap
  (match l
    (nil nil)
    ((f . r) (cons (bt->n f) (lob->heap r)))))

(check= (lob->heap '()) '())
(check= (lob->heap '((1))) '(1))
(check= (lob->heap '((1) (0))) '(1 0))
(check= (lob->heap '((1 0 1 1 1) (0) (1 0 1 0) (1 1 1 0))) '(23 0 10 14))

(defdata winner-nim (oneof -1 0 1))

; represents state of game
; change to struct in future
(defdata game (list bit heap winner-nim))

; KEY:
; (first game) <- player
; (second game) <- state of game
; (third game) <- winner
  
(definec switch-player (b :bit) :bit
  (if (== b 0)
    1
    0))

(check= (switch-player 0) 1)
(check= (switch-player 1) 0)

; takes piece from first heap with smaller nim-sum than og size. If the smallest is 0,
; removes it since the heap is done
(definec take-smallest (og new acc :heap) :heap
  :ic (== (len og) (len new))
  (match og 
    (nil acc)
    ((f . r) (if (< (first new) f)
               (if (== (first new) 0)
                 (app acc r)
                 (app acc (list (first new)) r))
               (take-smallest r (rest new) (app acc (list f)))))))


(check= (take-smallest '() '() '()) '())
(check= (take-smallest '() '() '(1 2)) '(1 2))
(check= (take-smallest '(1 2 4) '(1 2 4) '()) '(1 2 4))
(check= (take-smallest '(1 2 4) '(2 3 5) '()) '(1 2 4))
(check= (take-smallest '(1 2 4) '(2 1 5) '()) '(1 1 4))
(check= (take-smallest '(1 2 4) '(2 0 5) '()) '(1 4))

; move when only 2 heaps left
(definec two-heap-move (h :heap) :heap
  :ic (== (len h) 2) 
  (cond ((== (first h) (second h)) (if (posp (first h))
                                     (list (1- (first h)) (second h))
                                     '()))
        ((> (first h) (second h)) (list (second h) (second h)))
        (t (list (first h) (first h)))))

(check= (two-heap-move '(1 1)) '(0 1))
(check= (two-heap-move '(3 1)) '(1 1))
(check= (two-heap-move '(2 3)) '(2 2))

; subtract one from first heap in game state
(definec sub-one (g :game) :game
  :ic (^ (> (len (second g)) 2) (posp (first (second g))))
  (if (== (first (second g)) 1)
    (list (switch-player (first g)) (rest (second g)) -1)
    (list (switch-player (first g)) (cons (1- (first (second g))) (rest (second g))) -1)))

; single move in general
(definec opt-move (g :game) :game
  :ic (posp (len (second g)))
  :skip-tests t
  :skip-function-contractp t
  :skip-body-contractsp t
  (cond ((== 1 (len (second g))) (list (first g) '() (first g)))
        ((== 2 (len (second g))) (list (switch-player (first g)) (two-heap-move (second g)) -1))
        (t (let* ((nim-sum-n (xor-bin (heap->lob (second g)) (len (heap->lob (second g)))))
                  (nim-sum-b (n->bt nim-sum-n)))
             (if (!= 0 nim-sum-n)
               (let* ((ns-h-b (xor-lob-val (heap->lob (second g)) nim-sum-b))
                      (ns-h-n (lob->heap ns-h-b)))
                 (list (switch-player (first g)) (take-smallest (second g) ns-h-n '()) -1))
               (sub-one g))))))

(check= (opt-move '(1 (1 2) -1)) (list 0 '(1 1) -1))
(check= (opt-move '(1 (1) -1)) (list 1 '() 1))
(check= (opt-move '(1 (1 2 3) -1)) '(0 (2 3) -1))
(check= (opt-move '(1 (2 2 3) -1)) '(0 (1 2 3) -1))
(check= (opt-move '(0 (3 7 8 10 12) -1)) '(1 (3 7 2 10 12) -1))
(check= (opt-move '(0 (3 7 8 10 12) 1)) '(1 (3 7 2 10 12) -1))

(defdata log (listof game))

(definec no-zeros (input :heap) :bool
  (match input
    (nil t)
    ((f . r) (if (== f 0)
               nil
               (no-zeros r)))))
(check= (no-zeros '(1)) t)
(check= (no-zeros '(1 1 2)) t)
(check= (no-zeros '(1 1 0)) nil)

(definec red-from-idx (h :heap idx :nat acc :heap) :heap
  :ic (< idx (len h)) 
  (if (== idx 0)
    (if (== (first h) 0)
      (app acc (rest h))
      (app (app acc (list (1- (first h)))) (rest h)))
    (red-from-idx (rest h) (1- idx) (app acc (list (first h))))))

(check= (red-from-idx '(1) 0 '()) '(0))
(check= (red-from-idx '(1 2 3 4) 2 '()) '(1 2 2 4))
(check= (red-from-idx '(1 2 0 4) 2 '()) '(1 2 4))
(check= (red-from-idx '(1 56 70 2 4 6) 1 '()) '(1 55 70 2 4 6))
(check= (red-from-idx '(1 2 1 4) 2 '()) '(1 2 0 4))

(definec get-val (h :heap idx :nat) :nat
  :ic (< idx (len h)) 
  (if (== idx 0)
    (first h)
    (get-val (rest h) (1- idx))))

(check= (get-val '(1) 0) 1)
(check= (get-val '(1 2 3) 1) 2)
(check= (get-val '(1 2 3 4) 3) 4)

(definec rem-zero-size-heaps-h (h :heap) :heap
  (match h
    (nil nil)
    ((f . r) (if (== f 0)
               (rem-zero-size-heaps-h r)
               (cons f (rem-zero-size-heaps-h r))))))
(check= (rem-zero-size-heaps-h nil) '())
(check= (rem-zero-size-heaps-h '(1 2 3)) '(1 2 3))
(check= (rem-zero-size-heaps-h '(1 0 2 0 3)) '(1 2 3))

(definec rem-zero-size-heaps-log (g :log) :log
  (match g
    (nil nil)
    ((f . r) (cons (list (first f) (rem-zero-size-heaps-h (second f)) (third f))
                   (rem-zero-size-heaps-log r)))))
(check= (rem-zero-size-heaps-log nil) nil)
(check= (rem-zero-size-heaps-log '((1 (1 2 3) -1) (1 (1 2 0 0 0 3) -1) (1 (1 0 2 3) -1))) 
        '((1 (1 2 3) -1) (1 (1 2 3) -1) (1 (1 2 3) -1)))

(definec all-poss-one-idx (g :game idx :nat acc :log) :log
  :ic (< idx (len (second g)))
  :skip-admissibilityp t
  :skip-body-contractsp t
  (if (== 0 (get-val (second g) idx))
    (rem-zero-size-heaps-log acc)
    (all-poss-one-idx (list (first g) (red-from-idx (second g) idx '()) (third g))
                      idx
                      (append acc (list (list (first g) (red-from-idx (second g) idx '()) (third g)))))))
  
(check= (all-poss-one-idx (list 1 (list 2 3 4) -1) 0 '()) '((1 (1 3 4) -1) (1 (3 4) -1)))

(definec check-for-win (g :game) :game
  (if (endp (second g))
    (list (first g) nil (first g))
    g))

(check= (check-for-win '(1 (1 2) -1)) '(1 (1 2) -1))
(check= (check-for-win '(1 () -1)) '(1 () 1))
(check= (check-for-win '(0 () -1)) '(0 () 0))

(definec check-for-win-log (g :log) :log
  (match g
    (nil nil)
    ((f . r) (cons (check-for-win f) (check-for-win-log r)))))

(definec all-combos-game-start (g :game idx :nat) :log
  :ic (<= idx (len (second g)))
  :skip-tests t
  :skip-admissibilityp t
  :skip-function-contractp t
  :skip-body-contractsp t
  (if (== idx (len (second g)))
    nil
    (check-for-win-log (append (all-poss-one-idx g idx '()) (all-combos-game-start g (1+ idx))))))

(definec all-combos-game-pre-switch (g :game) :log
  (all-combos-game-start g 0))

(check= (all-combos-game-pre-switch '(1 (1 2 3) -1)) 
        '((1 (2 3) -1)
          (1 (1 1 3) -1)
          (1 (1 3) -1)
          (1 (1 2 2) -1)
          (1 (1 2 1) -1)
          (1 (1 2) -1)))

(check= (all-combos-game-pre-switch '(1 (3) -1)) 
        '((1 (2) -1)
          (1 (1) -1)
          (1 () 1)))

(definec switch-player-log (g :log) :log
  (match g
    (nil nil)
    ((f . r) (cons (list (switch-player (first f)) (second f) (third f))
                   (switch-player-log r)))))

(check= (switch-player-log '((1 () -1))) '((0 () -1)))
(check= (switch-player-log '((1 () -1) (0 () -1) (1 () -1))) '((0 () -1) (1 () -1) (0 () -1)))

(definec all-combos-game (g :game) :log
  (switch-player-log (all-combos-game-pre-switch g)))

(check= (all-combos-game '(1 (1 2 3) -1)) 
        '((0 (2 3) -1)
          (0 (1 1 3) -1)
          (0 (1 3) -1)
          (0 (1 2 2) -1)
          (0 (1 2 1) -1)
          (0 (1 2) -1)))

(check= (all-combos-game '(1 (3) -1)) 
        '((0 (2) -1)
          (0 (1) -1)
          (0 () 1)))

(definec all-combos-log (g :log) :log
  (match g
    (nil nil)
    ((f . r) (append (all-combos-game f) (all-combos-log r)))))

(check= (all-combos-log '((1 (2 3) -1) (1 (1 1 3) -1)))
        '((0 (1 3) -1)
          (0 (3) -1)
          (0 (2 2) -1)
          (0 (2 1) -1)
          (0 (2) -1)
          (0 (1 3) -1)
          (0 (1 3) -1)
          (0 (1 1 2) -1)
          (0 (1 1 1) -1)
          (0 (1 1) -1)))

(check= (all-combos-log '((1 (2) -1) (1 (1 1 3) -1)))
        '((0 (1) -1)
          (0 () 1)
          (0 (1 3) -1)
          (0 (1 3) -1)
          (0 (1 1 2) -1)
          (0 (1 1 1) -1)
          (0 (1 1) -1)))

(definec all-pos-len (g :log) :bool
  (match g
    (nil t)
    ((f . r) (if (posp (len (second f)))
               (all-pos-len r)
               nil))))

(definec apply-opt-move (g :log) :log
  :ic (all-pos-len g)
  :skip-tests t
  :skip-admissibilityp t
  :skip-function-contractp t
  :skip-body-contractsp t
  (match g
    (nil nil)
    ((f . r) (cons (opt-move f) (apply-opt-move r)))))

(check= (apply-opt-move '((1 (2 3) -1)
                          (1 (1 1 3) -1)
                          (1 (1 3) -1)
                          (1 (1 2 2) -1)
                          (1 (1 2 1) -1)
                          (1 (1 2) -1)))
        '((0 (2 2) -1)
         (0 (1 1) -1)
         (0 (1 1) -1)
         (0 (2 2) -1)
         (0 (1 1) -1)
         (0 (1 1) -1)))

(definec play-first-move (g :game) :log
  :ic (posp (len (second g)))
  :skip-admissibilityp t
  :skip-function-contractp t
  :skip-body-contractsp t
  (if (== 0 (first g))
    (list (opt-move g))
    (all-combos-game g)))

(check= (play-first-move '(1 (1 2 3) -1)) 
        '((0 (2 3) -1)
          (0 (1 1 3) -1)
          (0 (1 3) -1)
          (0 (1 2 2) -1)
          (0 (1 2 1) -1)
          (0 (1 2) -1)))
(check= (play-first-move '(0 (1 2 3) -1)) '((1 (2 3) -1))) 

(definec play-move (g :log) :log
  :ic (all-pos-len g)
  :skip-admissibilityp t
  :skip-function-contractp t
  :skip-body-contractsp t
  (match g
    (nil nil)
    ((f . &) (if (== (first f) 0)
               (apply-opt-move g)
               (all-combos-log g)))))

(check= (play-move '((1 (2 3) -1)
                     (1 (1 1 3) -1)
                     (1 (1 3) -1)
                     (1 (1 2 2) -1)
                     (1 (1 2 1) -1)
                     (1 (1 2) -1)))
        '((0 (1 3) -1)
          (0 (3) -1)
          (0 (2 2) -1)
          (0 (2 1) -1)
          (0 (2) -1)
          (0 (1 3) -1)
          (0 (1 3) -1)
          (0 (1 1 2) -1)
          (0 (1 1 1) -1)
          (0 (1 1) -1)
          (0 (3) -1)
          (0 (1 2) -1)
          (0 (1 1) -1)
          (0 (1) -1)
          (0 (2 2) -1)
          (0 (1 1 2) -1)
          (0 (1 2) -1)
          (0 (1 2 1) -1)
          (0 (1 2) -1)
          (0 (2 1) -1)
          (0 (1 1 1) -1)
          (0 (1 1) -1)
          (0 (1 2) -1)
          (0 (2) -1)
          (0 (1 1) -1)
          (0 (1) -1))
        )

(check= (play-move '((0 (2 3) -1)
                     (0 (1 1 3) -1)
                     (0 (1 3) -1)
                     (0 (1 2 2) -1)
                     (0 (1 2 1) -1)
                     (0 (1 2) -1)))
        '((1 (2 2) -1)
          (1 (1 1) -1)
          (1 (1 1) -1)
          (1 (2 2) -1)
          (1 (1 1) -1)
          (1 (1 1) -1)))

(check= (play-move '((1 (2) -1)
                     (1 (1 1 3) -1)
                     (1 (1 3) -1)
                     (1 (1 2 2) -1)
                     (1 (1 2 1) -1)
                     (1 (1 2) -1)))
        '((0 (1) -1)
          (0 nil 1)
          (0 (1 3) -1)
          (0 (1 3) -1)
          (0 (1 1 2) -1)
          (0 (1 1 1) -1)
          (0 (1 1) -1)
          (0 (3) -1)
          (0 (1 2) -1)
          (0 (1 1) -1)
          (0 (1) -1)
          (0 (2 2) -1)
          (0 (1 1 2) -1)
          (0 (1 2) -1)
          (0 (1 2 1) -1)
          (0 (1 2) -1)
          (0 (2 1) -1)
          (0 (1 1 1) -1)
          (0 (1 1) -1)
          (0 (1 2) -1)
          (0 (2) -1)
          (0 (1 1) -1)
          (0 (1) -1)))

(definec all-nil-have-winner (g :log) :bool
  (match g
    (nil t)
    ((f . r) (if (and (endp (rem-zero-size-heaps-h (second f))) (or (== (third f) -1) (== (first f) (third f))))
               nil
               (all-nil-have-winner r)))))

(check= (all-nil-have-winner '((0 (2 3) -1)
                     (0 (1 1 3) -1)
                     (0 (1 3) -1)
                     (0 (1 2 2) -1)
                     (0 (1 2 1) -1)
                     (0 (1 2) -1))) t)
(check= (all-nil-have-winner '((0 (2 3) -1)
                     (0 (1 1 3) -1)
                     (0 () -1)
                     (0 (1 2 2) -1)
                     (0 (1 2 1) -1)
                     (0 (1 2) -1))) nil)
(check= (all-nil-have-winner '((0 (2 3) -1)
                     (0 (1 1 3) -1)
                     (0 (0 0 0) -1)
                     (0 (1 2 2) -1)
                     (0 (1 2 1) -1)
                     (0 (1 2) -1))) nil)
(check= (all-nil-have-winner '((0 (2 3) -1)
                     (0 (1 1 3) -1)
                     (0 () 0)
                     (0 (1 2 2) -1)
                     (0 (1 2 1) -1)
                     (0 (1 2) -1))) nil)
(check= (all-nil-have-winner '((0 (2 3) -1)
                     (0 (1 1 3) -1)
                     (0 () 1)
                     (0 (1 2 2) -1)
                     (0 (1 2 1) -1)
                     (0 (1 2) -1))) t)

(definec ongoing-games-no-winner (g :log) :bool
  :skip-admissibilityp t
  :skip-function-contractp t
  :skip-body-contractsp t
  (let ((s-game (rem-zero-size-heaps-log g)))
    (match s-game
      (nil t)
      ((f . r) (if (and (!(endp (second f))) (!= (third f) -1))
                 nil
                 (ongoing-games-no-winner r))))))

(check= (ongoing-games-no-winner '((0 (1 2 3) 1))) nil)
(check= (ongoing-games-no-winner '((0 (1 2 3) -1) (0 (1 2 3) -1) (0 (1 2 3) -1))) t)
(check= (ongoing-games-no-winner '((0 () -1) (0 (1 2 3) -1) (0 (1 2 3) -1))) t)                 

(definec play-game-acc (g :log acc :log) :log
  :skip-admissibilityp t
  :skip-function-contractp t
  :skip-body-contractsp t
  (let* ((s-game (rem-zero-size-heaps-log g)))
    (match s-game
      (nil acc)
      ((f . r) (cond 
                ((or (== (third f) 0) (== (third f) 1)) 
                 (play-game-acc r (cons f acc)))
                ((endp (second f)) 
                 (play-game-acc r (cons f acc)))
                (t (play-game-acc (append (play-first-move f) r) acc)))))))
       
(definec play-game (g :game) :log
  (play-game-acc (list g) '()))

(check= (play-game '(1 (1 2 3) -1))
        '((0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)))
(check= (play-game '(0 (1 2 3) -1))
        '((0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 1)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)))

(definec all-won-comp (g :log) :bool
  (match g
    (nil t)
    ((f . r) (if (== (third f) 0)
               (all-won-comp r)
               nil))))
(check= (all-won-comp 
        '((0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0))) t)
(check= (all-won-comp 
        '((0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 1)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0)
          (0 nil 0))) nil)

(definec how-many-1-won (g :log) :nat
  (match g
    (nil 0)
    ((f . r) (if (== (third f) 1)
               (1+ (how-many-1-won r))
               (how-many-1-won r)))))#|ACL2s-ToDo-Line|#

   
