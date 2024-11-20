;$ACL2s-SMode$;ACL2s
(in-package "ACL2S")

; Represents the individual object in a heap
(defdata object nat)

; Represents a heap 
(defdata heap (listof object))

; Represents binary representation of number 
(defdata bit (oneof 0 1))
(defdata binary (listof bit))

; Converts nat -> binary
(definec ntb-helper (n :nat b :binary) :binary
  (if (zp n)
    b
    (ntb-helper (floor n 2) (cons (mod n 2) b))))

(check= (ntb-helper 0 '()) '())
(check= (ntb-helper 6 '()) '(1 1 0))
(check= (ntb-helper 10 '()) '(1 0 1 0))
(check= (ntb-helper 10 '(1)) '(1 0 1 0 1))

;; n->bt: Nat --> Binary
(definec n->bt (n :nat) :binary
  (if (== n 0)
    '(0)
    (ntb-helper n '())))

(check= (n->bt 0)  '(0))
(check= (n->bt 6)  '(1 1 0))
(check= (n->bt 10) '(1 0 1 0))
(check= (n->bt 17) '(1 0 0 0 1))

; Loops for bit -> n 
(definec forloop (bv :binary power total-sum :nat) :nat
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

; Binary -> nat
(definec bt->n (bin :binary) :nat
  (forloop (lrev bin) 0 0))

(check= (bt->n '(1 0 1 0)) 10)  
(check= (bt->n '(1 1 1)) 7) 
(check= (bt->n '(1 0 0)) 4) 
(check= (bt->n '(1 1 1 1 1)) 31) 
(check= (bt->n ()) 0)

; list of binary, representing the heaps
(defdata lob (listof binary))

; adds an arbitrary number of zeros to b. Used for making 2 binary numbers equal length
(definec add-zeros (b :binary n :nat) :binary
  (if (== n 0)
    b
    (add-zeros (cons 0 b) (1- n))))

(check= (add-zeros '() 0) '())
(check= (add-zeros '() 2) '(0 0))
(check= (add-zeros '(1 0) 0) '(1 0))
(check= (add-zeros '(1 0) 2) '(0 0 1 0))

; makes 2 binary numbers the same length. Used to perform the xor operation on them.
(definec make-same-len (b1 b2 :binary) :lob
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
(definec xor-two-bin-help (b1 b2 :binary output :binary) :binary
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

(definec xor-two-bin (b1 b2 :binary) :binary
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
(definec xor-lob-val (bins :lob b :binary) :lob
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
  :ic (^ (== (len h) 2) (posp (first h)) (posp (second h)))
  (cond ((== (first h) (second h)) (list (1- (first h)) (second h)))
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
    (list (switch-player (first g)) (cons (1- (first (second g))) (rest (second g))) -1)))#|ACL2s-ToDo-Line|#


; single move in general
(definec opt-move (g :game) :game
  :ic (posp (len (second g)))
  (cond ((== 1 (len (second g))) (list (first g) '() (first g)))
        ((== 2 (len (second g))) (list (switch-player (first g)) (two-heap-move (second g)) -1))
        (t (let* ((nim-sum-n (xor-bin (heap->lob (second g)) (len (heap->lob (second g)))))
                  (nim-sum-b (n->bt nim-sum-n)))
             (if (== 0 nim-sum-n)
               (sub-one g)
               (let* ((ns-h-b (xor-lob-val (second g) nim-sum-b))
                      (ns-h-n (lob->heap ns-h-b)))
                 (list (switch-player (first g)) (take-smallest (second g) ns-h-n '()) -1)))))))
      
         






   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   