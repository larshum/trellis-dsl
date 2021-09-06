include "seq.mc"

let min3 = lam a. lam b. lam c.
  if lti a b then
    if lti a c then a else c
  else
    if lti b c then b else c

recursive let levenshtein = lam s1. lam s2.
  if gti (length s1) (length s2) then levenshtein s2 s1
  else
    let n = addi (length s1) 1 in
    let m = addi (length s2) 1 in
    recursive let levenshteinRow = lam i. lam prev. lam curr.
      if eqi i m then prev
      else
        let curr =
          mapi
            (lam j. lam.
              if eqi j 0 then i
              else
                let del = addi (get prev j) 1 in
                let ins = addi (get curr (subi j 1)) 1 in
                let sub =
                  if eqc (get s1 (subi j 1)) (get s2 (subi i 1)) then
                    get prev (subi j 1)
                  else
                    addi (get prev (subi j 1)) 1
                in
                min3 del ins sub)
            curr
        in
        levenshteinRow (addi i 1) curr prev
    in
    let prev = create n (lam i. i) in
    let curr = create n (lam. 0) in
    get (levenshteinRow 1 prev curr) (length s1)
end

utest levenshtein "" "" with 0
utest levenshtein "massa" "maska" with 1
utest levenshtein "kitten" "sitting" with 3
utest levenshtein "ACGT" "GCT" with 2
