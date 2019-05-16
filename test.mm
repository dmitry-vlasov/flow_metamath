

  $( Declare the primitive constant symbols for propositional calculus. $)

    $( Define the syntax and logical typecodes, and declare that our grammar is
     unambiguous (verifiable using the KLR parser, with compositing depth 5).
     (This j comment need not be read by verifiers, but is useful for parsers
     like mmj2.) $)
  $(
    syntax 'wff';
    syntax '|-' as 'wff';
    unambiguous 'klr 5';
  $)
  
$c |- $.
$c ( $.
$c ) $.
$c -> $.
$c -. $.
$c wff $.

${
	$v ph  $.
	f0_wn  $f wff ph $.
	a_wn $a wff -. ph $.
$}

${
	$v ph ps  $.
	f0_wi  $f wff ph $.
	f1_wi  $f wff ps $.
	a_wi $a wff ( ph -> ps ) $.
$}

${
	$v ph ps  $.
	f0_ax-1  $f wff ph $.
	f1_ax-1  $f wff ps $.
	a_ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
$}

${
	$v ph ps ch  $.
	f0_ax-2  $f wff ph $.
	f1_ax-2  $f wff ps $.
	f2_ax-2  $f wff ch $.
	a_ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
$}

${
	$v ph ps  $.
	f0_ax-3  $f wff ph $.
	f1_ax-3  $f wff ps $.
	a_ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.
$}

${
	$v ph ps  $.
	f0_ax-mp  $f wff ph $.
	f1_ax-mp  $f wff ps $.
	e0_ax-mp $e |- ph $.
	e1_ax-mp $e |- ( ph -> ps ) $.
	a_ax-mp $a |- ps $.
$}

${
	$v ph ps ch  $.
	f0_mp2b  $f wff ph $.
	f1_mp2b  $f wff ps $.
	f2_mp2b  $f wff ch $.
	e0_mp2b $e |- ph $.
	e1_mp2b $e |- ( ph -> ps ) $.
	e2_mp2b $e |- ( ps -> ch ) $.
	p_mp2b $p |- ch $=
	f1_mp2b f2_mp2b f0_mp2b f1_mp2b e0_mp2b e1_mp2b a_ax-mp e2_mp2b a_ax-mp $.
$}

${
	$v ph ps  $.
	f0_a1i  $f wff ph $.
	f1_a1i  $f wff ps $.
	e0_a1i $e |- ph $.
	p_a1i $p |- ( ps -> ph ) $=
	f0_a1i f1_a1i f0_a1i a_wi e0_a1i f0_a1i f1_a1i a_ax-1 a_ax-mp $.
$}

$(  Drop and replace an antecedent.  (Contributed by Stefan O'Rear,
       29-Jan-2015.)   $)

${
	$v ph ps ch  $.
	f0_mp1i  $f wff ph $.
	f1_mp1i  $f wff ps $.
	f2_mp1i  $f wff ch $.
	e0_mp1i $e |- ph $.
	e1_mp1i $e |- ( ph -> ps ) $.
	p_mp1i $p |- ( ch -> ps ) $=
	f1_mp1i f2_mp1i f0_mp1i f1_mp1i e0_mp1i e1_mp1i a_ax-mp p_a1i $.
$}

$(  Premise for ~ a2i .   $)

$(  Inference derived from axiom ~ ax-2 .  (Contributed by NM,
       5-Aug-1993.)   $)

${
	$v ph ps ch  $.
	f0_a2i  $f wff ph $.
	f1_a2i  $f wff ps $.
	f2_a2i  $f wff ch $.
	e0_a2i $e |- ( ph -> ( ps -> ch ) ) $.
	p_a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $=
	f0_a2i f1_a2i f2_a2i a_wi a_wi f0_a2i f1_a2i a_wi f0_a2i f2_a2i a_wi a_wi e0_a2i f0_a2i f1_a2i f2_a2i a_ax-2 a_ax-mp $.
$}

$(  Inference adding common antecedents in an implication.  (Contributed by
       NM, 5-Aug-1993.)   $)

${
	$v ph ps ch  $.
	f0_imim2i  $f wff ph $.
	f1_imim2i  $f wff ps $.
	f2_imim2i  $f wff ch $.
	e0_imim2i $e |- ( ph -> ps ) $.
	p_imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $=
	f2_imim2i f0_imim2i f1_imim2i f0_imim2i f1_imim2i a_wi f2_imim2i e0_imim2i p_a1i p_a2i $.
$}

$(  A modus ponens deduction.  A translation of natural deduction rule
       ` -> ` E ( ` -> ` elimination), see ~ natded .  (Contributed by NM,
       5-Aug-1993.)   $)

${
	$v ph ps ch  $.
	f0_mpd  $f wff ph $.
	f1_mpd  $f wff ps $.
	f2_mpd  $f wff ch $.
	e0_mpd $e |- ( ph -> ps ) $.
	e1_mpd $e |- ( ph -> ( ps -> ch ) ) $.
	p_mpd $p |- ( ph -> ch ) $=
	f0_mpd f1_mpd a_wi f0_mpd f2_mpd a_wi e0_mpd f0_mpd f1_mpd f2_mpd e1_mpd p_a2i a_ax-mp $.
$}

$(  First of 2 premises for ~ syl .   $)

$(  Second of 2 premises for ~ syl .   $)

$(  An inference version of the transitive laws for implication ~ imim2 and
       ~ imim1 , which Russell and Whitehead call "the principle of the
       syllogism...because...the syllogism in Barbara is derived from them"
       (quote after Theorem *2.06 of [WhiteheadRussell] p. 101).  Some authors
       call this law a "hypothetical syllogism."

       (A bit of trivia: this is the most commonly referenced assertion in our
       database.  In second place is ~ eqid , followed by ~ syl2anc ,
       ~ adantr , ~ syl3anc , and ~ ax-mp .  The Metamath program command 'show
       usage' shows the number of references.)  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by O'Cat, 20-Oct-2011.)  (Proof shortened
       by Wolf Lammen, 26-Jul-2012.)   $)

${
	$v ph ps ch  $.
	f0_syl  $f wff ph $.
	f1_syl  $f wff ps $.
	f2_syl  $f wff ch $.
	e0_syl $e |- ( ph -> ps ) $.
	e1_syl $e |- ( ps -> ch ) $.
	p_syl $p |- ( ph -> ch ) $=
	f0_syl f1_syl f2_syl e0_syl f1_syl f2_syl a_wi f0_syl e1_syl p_a1i p_mpd $.
$}

$(  A nested modus ponens inference.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Stefan Allan, 20-Mar-2006.)   $)

${
	$v ph ps ch  $.
	f0_mpi  $f wff ph $.
	f1_mpi  $f wff ps $.
	f2_mpi  $f wff ch $.
	e0_mpi $e |- ps $.
	e1_mpi $e |- ( ph -> ( ps -> ch ) ) $.
	p_mpi $p |- ( ph -> ch ) $=
	f0_mpi f1_mpi f2_mpi f1_mpi f0_mpi e0_mpi p_a1i e1_mpi p_mpd $.
$}

$(  A double modus ponens inference.  (Contributed by NM, 5-Apr-1994.)
       (Proof shortened by Wolf Lammen, 23-Jul-2013.)   $)

${
	$v ph ps ch  $.
	f0_mp2  $f wff ph $.
	f1_mp2  $f wff ps $.
	f2_mp2  $f wff ch $.
	e0_mp2 $e |- ph $.
	e1_mp2 $e |- ps $.
	e2_mp2 $e |- ( ph -> ( ps -> ch ) ) $.
	p_mp2 $p |- ch $=
	f0_mp2 f2_mp2 e0_mp2 f0_mp2 f1_mp2 f2_mp2 e1_mp2 e2_mp2 p_mpi a_ax-mp $.
$}

$(  Inference chaining two syllogisms.  (Contributed by NM, 5-Aug-1993.)   $)

${
	$v ph ps ch th  $.
	f0_3syl  $f wff ph $.
	f1_3syl  $f wff ps $.
	f2_3syl  $f wff ch $.
	f3_3syl  $f wff th $.
	e0_3syl $e |- ( ph -> ps ) $.
	e1_3syl $e |- ( ps -> ch ) $.
	e2_3syl $e |- ( ch -> th ) $.
	p_3syl $p |- ( ph -> th ) $=
	f0_3syl f2_3syl f3_3syl f0_3syl f1_3syl f2_3syl e0_3syl e1_3syl p_syl e2_3syl p_syl $.
$}

$(  Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  For
     another version of the proof directly from axioms, see ~ id1 .
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Stefan Allan,
     20-Mar-2006.)   $)

${
	$v ph  $.
	f0_id  $f wff ph $.
	p_id $p |- ( ph -> ph ) $=
	f0_id f0_id f0_id a_wi f0_id f0_id f0_id a_ax-1 f0_id f0_id f0_id a_wi a_ax-1 p_mpd $.
$}

$(  Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  This
     version is proved directly from the axioms for demonstration purposes.
     This proof is a popular example in the literature and is identical, step
     for step, to the proofs of Theorem 1 of [Margaris] p. 51, Example 2.7(a)
     of [Hamilton] p. 31, Lemma 10.3 of [BellMachover] p. 36, and Lemma 1.8 of
     [Mendelson] p. 36.  It is also "Our first proof" in Hirst and Hirst's _A
     Primer for Logic and Proof_ p. 17 (PDF p. 23) at
     ~ http://www.mathsci.appstate.edu/~~hirstjl/primer/hirst.pdf .  For a
     shorter version of the proof that takes advantage of previously proved
     theorems, see ~ id .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.)  (Proof modification is discouraged.)   $)

${
	$v ph  $.
	f0_id1  $f wff ph $.
	p_id1 $p |- ( ph -> ph ) $=
	f0_id1 f0_id1 f0_id1 a_wi a_wi f0_id1 f0_id1 a_wi f0_id1 f0_id1 a_ax-1 f0_id1 f0_id1 f0_id1 a_wi f0_id1 a_wi a_wi f0_id1 f0_id1 f0_id1 a_wi a_wi f0_id1 f0_id1 a_wi a_wi f0_id1 f0_id1 f0_id1 a_wi a_ax-1 f0_id1 f0_id1 f0_id1 a_wi f0_id1 a_ax-2 a_ax-mp a_ax-mp $.
$}

$(  Principle of identity with antecedent.  (Contributed by NM,
     26-Nov-1995.)   $)

${
	$v ph ps  $.
	f0_idd  $f wff ph $.
	f1_idd  $f wff ps $.
	p_idd $p |- ( ph -> ( ps -> ps ) ) $=
	f1_idd f1_idd a_wi f0_idd f1_idd p_id p_a1i $.
$}

$(  Deduction introducing an embedded antecedent.

       _Naming convention_:  We often call a theorem a "deduction" and suffix
       its label with "d" whenever the hypotheses and conclusion are each
       prefixed with the same antecedent.  This allows us to use the theorem in
       places where (in traditional textbook formalizations) the standard
       Deduction Theorem would be used; here ` ph ` would be replaced with a
       conjunction ( ~ df-an ) of the hypotheses of the would-be deduction.  By
       contrast, we tend to call the simpler version with no common antecedent
       an "inference" and suffix its label with "i"; compare theorem ~ a1i .
       Finally, a "theorem" would be the form with no hypotheses; in this case
       the "theorem" form would be the original axiom ~ ax-1 .  We usually show
       the theorem form without a suffix on its label (e.g. ~ pm2.43 vs.
       ~ pm2.43i vs. ~ pm2.43d ).  When an inference is converted to a theorem
       by eliminating an "is a set" hypothesis, we sometimes suffix the theorem
       form with "g" (for "more general") as in ~ uniex vs. ~ uniexg .
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Stefan Allan,
       20-Mar-2006.)   $)

${
	$v ph ps ch  $.
	f0_a1d  $f wff ph $.
	f1_a1d  $f wff ps $.
	f2_a1d  $f wff ch $.
	e0_a1d $e |- ( ph -> ps ) $.
	p_a1d $p |- ( ph -> ( ch -> ps ) ) $=
	f0_a1d f1_a1d f2_a1d f1_a1d a_wi e0_a1d f1_a1d f2_a1d a_ax-1 p_syl $.
$}

$(  Deduction distributing an embedded antecedent.  (Contributed by NM,
       23-Jun-1994.)   $)

${
	$v ph ps ch th  $.
	f0_a2d  $f wff ph $.
	f1_a2d  $f wff ps $.
	f2_a2d  $f wff ch $.
	f3_a2d  $f wff th $.
	e0_a2d $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	p_a2d $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $=
	f0_a2d f1_a2d f2_a2d f3_a2d a_wi a_wi f1_a2d f2_a2d a_wi f1_a2d f3_a2d a_wi a_wi e0_a2d f1_a2d f2_a2d f3_a2d a_ax-2 p_syl $.
$}

$(  Add two antecedents to a wff.  (Contributed by Jeff Hankins,
       4-Aug-2009.)  (Proof shortened by Wolf Lammen, 23-Jul-2013.)   $)

${
	$v ph ps ch  $.
	f0_a1ii  $f wff ph $.
	f1_a1ii  $f wff ps $.
	f2_a1ii  $f wff ch $.
	e0_a1ii $e |- ch $.
	p_a1ii $p |- ( ph -> ( ps -> ch ) ) $=
	f0_a1ii f2_a1ii f1_a1ii f2_a1ii f0_a1ii e0_a1ii p_a1i p_a1d $.
$}

$(  Syllogism inference with commutation of antecedents.  (Contributed by
       NM, 29-Aug-2004.)  (Proof shortened by O'Cat, 2-Feb-2006.)  (Proof
       shortened by Stefan Allan, 23-Feb-2006.)   $)

${
	$v ph ps ch th  $.
	f0_sylcom  $f wff ph $.
	f1_sylcom  $f wff ps $.
	f2_sylcom  $f wff ch $.
	f3_sylcom  $f wff th $.
	e0_sylcom $e |- ( ph -> ( ps -> ch ) ) $.
	e1_sylcom $e |- ( ps -> ( ch -> th ) ) $.
	p_sylcom $p |- ( ph -> ( ps -> th ) ) $=
	f0_sylcom f1_sylcom f2_sylcom a_wi f1_sylcom f3_sylcom a_wi e0_sylcom f1_sylcom f2_sylcom f3_sylcom e1_sylcom p_a2i p_syl $.
$}

$(  Syllogism inference with commuted antecedents.  (Contributed by NM,
       24-May-2005.)   $)

${
	$v ph ps ch th  $.
	f0_syl5com  $f wff ph $.
	f1_syl5com  $f wff ps $.
	f2_syl5com  $f wff ch $.
	f3_syl5com  $f wff th $.
	e0_syl5com $e |- ( ph -> ps ) $.
	e1_syl5com $e |- ( ch -> ( ps -> th ) ) $.
	p_syl5com $p |- ( ph -> ( ch -> th ) ) $=
	f0_syl5com f2_syl5com f1_syl5com f3_syl5com f0_syl5com f1_syl5com f2_syl5com e0_syl5com p_a1d e1_syl5com p_sylcom $.
$}

$(  Premise for ~ com12 .  See ~ pm2.04 for the theorem form.   $)

$(  Inference that swaps (commutes) antecedents in an implication.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen,
       4-Aug-2012.)   $)

${
	$v ph ps ch  $.
	f0_com12  $f wff ph $.
	f1_com12  $f wff ps $.
	f2_com12  $f wff ch $.
	e0_com12 $e |- ( ph -> ( ps -> ch ) ) $.
	p_com12 $p |- ( ps -> ( ph -> ch ) ) $=
	f1_com12 f1_com12 f0_com12 f2_com12 f1_com12 p_id e0_com12 p_syl5com $.
$}

$(  A syllogism rule of inference.  The first premise is used to replace the
       second antecedent of the second premise.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 25-May-2013.)   $)

${
	$v ph ps ch th  $.
	f0_syl5  $f wff ph $.
	f1_syl5  $f wff ps $.
	f2_syl5  $f wff ch $.
	f3_syl5  $f wff th $.
	e0_syl5 $e |- ( ph -> ps ) $.
	e1_syl5 $e |- ( ch -> ( ps -> th ) ) $.
	p_syl5 $p |- ( ch -> ( ph -> th ) ) $=
	f0_syl5 f2_syl5 f3_syl5 f0_syl5 f1_syl5 f2_syl5 f3_syl5 e0_syl5 e1_syl5 p_syl5com p_com12 $.
$}

$(  A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Wolf Lammen, 30-Jul-2012.)   $)

${
	$v ph ps ch th  $.
	f0_syl6  $f wff ph $.
	f1_syl6  $f wff ps $.
	f2_syl6  $f wff ch $.
	f3_syl6  $f wff th $.
	e0_syl6 $e |- ( ph -> ( ps -> ch ) ) $.
	e1_syl6 $e |- ( ch -> th ) $.
	p_syl6 $p |- ( ph -> ( ps -> th ) ) $=
	f0_syl6 f1_syl6 f2_syl6 f3_syl6 e0_syl6 f2_syl6 f3_syl6 a_wi f1_syl6 e1_syl6 p_a1i p_sylcom $.
$}

$(  Combine ~ syl5 and ~ syl6 .  (Contributed by NM, 14-Nov-2013.)   $)

${
	$v ph ps ch th ta  $.
	f0_syl56  $f wff ph $.
	f1_syl56  $f wff ps $.
	f2_syl56  $f wff ch $.
	f3_syl56  $f wff th $.
	f4_syl56  $f wff ta $.
	e0_syl56 $e |- ( ph -> ps ) $.
	e1_syl56 $e |- ( ch -> ( ps -> th ) ) $.
	e2_syl56 $e |- ( th -> ta ) $.
	p_syl56 $p |- ( ch -> ( ph -> ta ) ) $=
	f0_syl56 f1_syl56 f2_syl56 f4_syl56 e0_syl56 f2_syl56 f1_syl56 f3_syl56 f4_syl56 e1_syl56 e2_syl56 p_syl6 p_syl5 $.
$}

$(  Syllogism inference with commuted antecedents.  (Contributed by NM,
       25-May-2005.)   $)

${
	$v ph ps ch th  $.
	f0_syl6com  $f wff ph $.
	f1_syl6com  $f wff ps $.
	f2_syl6com  $f wff ch $.
	f3_syl6com  $f wff th $.
	e0_syl6com $e |- ( ph -> ( ps -> ch ) ) $.
	e1_syl6com $e |- ( ch -> th ) $.
	p_syl6com $p |- ( ps -> ( ph -> th ) ) $=
	f0_syl6com f1_syl6com f3_syl6com f0_syl6com f1_syl6com f2_syl6com f3_syl6com e0_syl6com e1_syl6com p_syl6 p_com12 $.
$}
