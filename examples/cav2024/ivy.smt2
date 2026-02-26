; benchmark generated from python API
(set-info :status unknown)
(declare-sort index)
 (declare-fun |0:index| () index)
(declare-fun @X () Int)
(declare-fun time.succ (Int Int) Bool)
(declare-fun |<:index:index| (index index) Bool)
(declare-fun index.succ (index index) Bool)
(assert
 (let (($x201 (forall ((|X:time| Int) (|Y:time| Int) )(= (time.succ |X:time| |Y:time|) (= |Y:time| (+ |X:time| 1))))
 ))
 (and $x201)))
(assert
 (let (($x23 (forall ((|X:index| index) (|Y:index| index) (|Z:index| index) )(let (($x92 (|<:index:index| |X:index| |Z:index|)))
 (let (($x282 (and $x92 (not (and (|<:index:index| |X:index| |Y:index|) (|<:index:index| |Y:index| |Z:index|))))))
 (let (($x135 (index.succ |X:index| |Z:index|)))
 (=> $x135 $x282)))))
 ))
 (and $x23)))
(assert
 (let (($x131 (forall ((|T:index| index) (|U:index| index) (|V:index| index) )(let (($x92 (|<:index:index| |T:index| |V:index|)))
 (=> (and (|<:index:index| |T:index| |U:index|) (|<:index:index| |U:index| |V:index|)) $x92)))
 ))
 (and $x131)))
(assert
 (let (($x10 (forall ((|T:index| index) (|U:index| index) )(not (and (|<:index:index| |T:index| |U:index|) (|<:index:index| |U:index| |T:index|))))
 ))
 (and $x10)))
(assert
 (let (($x109 (forall ((|T:index| index) (|U:index| index) )(let (($x46 (|<:index:index| |U:index| |T:index|)))
 (let (($x18 (|<:index:index| |T:index| |U:index|)))
 (or $x18 (= |T:index| |U:index|) $x46))))
 ))
 (and $x109)))
(assert
 (let (($x33 (forall ((|X:index| index) )(or (= |0:index| |X:index|) (|<:index:index| |0:index| |X:index|)))
 ))
 (and $x33)))
(assert
 (and (not (<= 0 @X)) (not (> 0 @X))))
(check-sat)
