; Quadratic equation test case generation script
; Covers 13 test scenarios, all automatically generated through constraints

; ----------------------------
; 1. Two distinct real roots (D > 0)
; ----------------------------
(push)
(echo "=== Test case: Two distinct real roots ===")
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and
    (not (= a 0.0))
    (> (- (* b b) (* 4.0 a c)) 0.0)
    (> (abs a) 0.1) (< (abs a) 10.0)
    (> (abs b) 0.1) (< (abs b) 10.0)
    (> (abs c) 0.1) (< (abs c) 10.0)
))
(check-sat)
(get-model)
(pop)

; ----------------------------
; 2. Single real root (D = 0)
; ----------------------------
(push)
(echo "=== Test case: Single real root ===")
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and
    (not (= a 0.0))
    (= (- (* b b) (* 4.0 a c)) 0.0)
    (> (abs b) 0.1)
))
(check-sat)
(get-model)
(pop)

; ----------------------------
; 3. Complex roots (D < 0)
; ----------------------------
(push)
(echo "=== Test case: Complex roots ===")
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and
    (not (= a 0.0))
    (< (- (* b b) (* 4.0 a c)) 0.0)
    (> (abs b) 0.1)
))
(check-sat)
(get-model)
(pop)

; ----------------------------
; 4. Very small a value
; ----------------------------
(push)
(echo "=== Test case: Very small positive a ===")
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and
    (> a (/ 1.0 10000000000.0)) ; a > 1e-10
    (< a (/ 1.0 1000000000.0))  ; a < 1e-9
    (not (= b 0.0))
))
(check-sat)
(get-model)
(pop)

(push)
(echo "=== Test case: Very small negative a ===")
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and
    (< a (/ -1.0 10000000000.0)) ; a < -1e-10
    (> a (/ -1.0 1000000000.0))  ; a > -1e-9
    (not (= b 0.0))
))
(check-sat)
(get-model)
(pop)

; ----------------------------
; 5. Large coefficient cases
; ----------------------------
(push)
(echo "=== Test case: Very large a coefficient ===")
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and
    (> a 100000000000000000000.0) ; a > 1e20
    (< b 100.0)
    (< c 100.0)
))
(check-sat)
(get-model)
(pop)

(push)
(echo "=== Test case: Very large b coefficient ===")
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and
    (> b 100000000000000000000.0) ; b > 1e20
    (< a 100.0)
    (< c 100.0)
))
(check-sat)
(get-model)
(pop)

; ----------------------------
; 6. b² much greater than 4ac
; ----------------------------
(push)
(echo "=== Test case: b² >> 4ac (large b) ===")
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and
    (> b 10000000000.0) ; b > 1e10
    (< (abs (* a c)) 0.0001) ; |ac| < 1e-4
))
(check-sat)
(get-model)
(pop)

(push)
(echo "=== Test case: b² >> 4ac (small ac) ===")
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and
    (> b 1.0)
    (< (abs (* a c)) (/ 1.0 10000000000.0)) ; |ac| < 1e-10
))
(check-sat)
(get-model)
(pop)

; ----------------------------
; 7. Fractional coefficient test (new)
; ----------------------------
(push)
(echo "=== Test case: Fractional coefficients ===")
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and
    (not (= (to_int a) a)) ; a is not integer
    (not (= (to_int b) b))
    (not (= (to_int c) c))
    (> (abs a) 0.1)
))
(check-sat)
(get-model)
(pop)

; ----------------------------
; 8. Extreme discriminant test (new)
; ----------------------------
(push)
(echo "=== Test case: Discriminant near zero ===")
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and
    (> (abs (- (* b b) (* 4.0 a c))) (/ 1.0 10000000000.0)) ; |D| > 1e-10
    (< (abs (- (* b b) (* 4.0 a c))) 0.0001) ; |D| < 1e-4
))
(check-sat)
(get-model)
(pop)

; ----------------------------
; 9. Floating-point precision boundary test (new)
; ----------------------------
(push)
(echo "=== Test case: Floating-point precision boundary ===")
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and
    (= a (/ 1.0 1073741824.0)) ; 2^-30
    (= b (/ 1.0 1048576.0))    ; 2^-20
    (= c (/ 1.0 1048576.0))    ; 2^-20
))
(check-sat)
(get-model)
(pop)

; ----------------------------
; 10. Special value combination test (new)
; ----------------------------
(push)
(echo "=== Test case: Special combination (a=1,b=0) ===")
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and
    (= a 1.0)
    (= b 0.0)
    (not (= c 0.0))
))
(check-sat)
(get-model)
(pop)

; ----------------------------
; 11. Denormal number test (new)
; ----------------------------
(push)
(echo "=== Test case: Denormal numbers ===")
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and
    (< (abs a) (/ 1.0 100000000000000000000.0)) ; |a| < 1e-20
    (> (abs b) 1.0)
))
(check-sat)
(get-model)
(pop)

; ----------------------------
; 12. Near-integer test (new)
; ----------------------------
(push)
(echo "=== Test case: Near-integer values ===")
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and
    (< (abs (- a (to_int a))) (/ 1.0 10000000000.0)) ; a is almost integer
    (> (abs b) 1.0)
))
(check-sat)
(get-model)
(pop)