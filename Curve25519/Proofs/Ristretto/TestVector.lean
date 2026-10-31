/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Ristretto.Encoding
import all Curve25519.Basic
import Curve25519.Proofs.Edwards.Certs
import Curve25519.Proofs.Ristretto.Certs
public section

/-! # The RFC 9496 §A.1 test vectors for the ristretto255 encoding (not audited)

Kernel checks (`decide +kernel`) of the encodings of the multiples `2 B, …, 15 B` of the
basepoint against RFC 9496 §A.1 (the encoding of `B` itself is `encodeRep_basepoint` in
`Curve25519.Ristretto.Encoding`): a regression test of `Ristretto.encodeRep`. For each `k`, the
coordinates of `k • basepoint` are certified by a projective-equality check of `Extended.nsmul`
(as in `Curve25519.Proofs.Edwards.Certs`), the inverse square root of `(1 + y)(1 - y)(x y)²` is
exhibited as a numeral, and the rest of RFC 9496 §4.3.2 is evaluated by the kernel.
`Curve25519.Basic` is imported with `import all` so that the kernel can unfold `p`, `sqrtM1` and
`invsqrtAMinusD`. -/

namespace curve25519.Proofs

open TwistedEdwardsModel

/-! ### `2 B` -/

private theorem two_nsmul_basepoint_x_y (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    (2 • P).x = 24727413235106541002554574571675588834622768167397638456726423682521233608206 ∧
      (2 • P).y = 15549675580280190176352668710449542251549572066445060580507079593062643049417 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

/-- RFC 9496 §A.1: the encoding of `2 B` is
`6a493210f7499cd17fecb510ae0cea23a110e8d5b901f8acadd3095c73a3b919`. -/
theorem encodeRep_two_nsmul_basepoint :
    Ristretto.encodeRep (2 • basepoint) =
      11635816016306827767395297108041383048417969937796188516319649271592942455146 := by
  obtain ⟨hx, hy⟩ := two_nsmul_basepoint_x_y curve25519.basepoint basepoint_x_eq basepoint_y_eq
  exact encodeRep_of_coords
    (r := 44983099649789203610693030478239648478500906748903471392021725998287843189168) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `3 B` -/

private theorem three_nsmul_basepoint_x_y (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    (3 • P).x = 46896733464454938657123544595386787789046198280132665686241321779790909858396 ∧
      (3 • P).y = 8324843778533443976490377120369201138301417226297555316741202210403726505172 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

/-- RFC 9496 §A.1: the encoding of `3 B` is
`94741f5d5d52755ece4f23f044ee27d5d1ea1e2bd196b462166b16152a9d0259`. -/
theorem encodeRep_three_nsmul_basepoint :
    Ristretto.encodeRep (3 • basepoint) =
      40260461926755251955718706939243089925229788613177830462037219643110335673492 := by
  obtain ⟨hx, hy⟩ := three_nsmul_basepoint_x_y curve25519.basepoint basepoint_x_eq basepoint_y_eq
  exact encodeRep_of_coords
    (r := 36497461975840538690775936217744539451560550655315987188433936599141694408376) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `4 B` -/

private theorem four_nsmul_basepoint_x_y (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    (4 • P).x = 14582954232372986451776170844943001818709880559417862259286374126315108956272 ∧
      (4 • P).y = 32483318716863467900234833297694612235682047836132991208333042722294373421359 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

/-- RFC 9496 §A.1: the encoding of `4 B` is
`da80862773358b466ffadfe0b3293ab3d9fd53c5ea6c955358f568322daf6a57`. -/
theorem encodeRep_four_nsmul_basepoint :
    Ristretto.encodeRep (4 • basepoint) =
      39539712639727764854030096366263363835037234367571502173881976170473752789210 := by
  obtain ⟨hx, hy⟩ := four_nsmul_basepoint_x_y curve25519.basepoint basepoint_x_eq basepoint_y_eq
  exact encodeRep_of_coords
    (r := 35035121287605745812010655531725244480097667362960576006075430377872208938292) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `5 B` -/

private theorem five_nsmul_basepoint_x_y (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    (5 • P).x = 33467004535436536005251147249499675200073690106659565782908757308821616914995 ∧
      (5 • P).y = 43097193783671926753355113395909008640284023746042808659097434958891230611693 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

/-- RFC 9496 §A.1: the encoding of `5 B` is
`e882b131016b52c1d3337080187cf768423efccbb517bb495ab812c4160ff44e`. -/
theorem encodeRep_five_nsmul_basepoint :
    Ristretto.encodeRep (5 • basepoint) =
      35711617013263642786200824652404949926957298723655034617396250384949589410536 := by
  obtain ⟨hx, hy⟩ := five_nsmul_basepoint_x_y curve25519.basepoint basepoint_x_eq basepoint_y_eq
  exact encodeRep_of_coords
    (r := 36864048792385267477785273181408709010075678839984391979759091284924269403108) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `6 B` -/

private theorem six_nsmul_basepoint_x_y (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    (6 • P).x = 34643617590234865996699167120328052565261792237873803846102513686264813449789 ∧
      (6 • P).y = 2399184961499513294557607325187831088545696902880432827228757905043131825908 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

/-- RFC 9496 §A.1: the encoding of `6 B` is
`f64746d3c92b13050ed8d80236a7f0007c3b3f962f5ba793d19a601ebb1df403`. -/
theorem encodeRep_six_nsmul_basepoint :
    Ristretto.encodeRep (6 • basepoint) =
      1788254424908918268483736458686471308637153583273756912236989785099523737590 := by
  obtain ⟨hx, hy⟩ := six_nsmul_basepoint_x_y curve25519.basepoint basepoint_x_eq basepoint_y_eq
  exact encodeRep_of_coords
    (r := 23597701923362501195997216484741126723870607845115886041667811608139015248572) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `7 B` -/

private theorem seven_nsmul_basepoint_x_y (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    (7 • P).x = 9199134265559022971505535402808359556995554859516252602543778295037484220679 ∧
      (7 • P).y = 22512087849695599276028560866629687720820254811233262850576678203618951717560 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

/-- RFC 9496 §A.1: the encoding of `7 B` is
`44f53520926ec81fbd5a387845beb7df85a96a24ece18738bdcfa6a7822a176d`. -/
theorem encodeRep_seven_nsmul_basepoint :
    Ristretto.encodeRep (7 • basepoint) =
      49343031373861346077246395661435597073206147504694015916602945883209739924804 := by
  obtain ⟨hx, hy⟩ := seven_nsmul_basepoint_x_y curve25519.basepoint basepoint_x_eq basepoint_y_eq
  exact encodeRep_of_coords
    (r := 42522262833952556978665942061542260250276734237943600715593307807815159555802) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `8 B` -/

private theorem eight_nsmul_basepoint_x_y (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    (8 • P).x = 46706390780465557264338673484185971070529246228527338942042475661633188627656 ∧
      (8 • P).y = 15299170165656271974649334809062094114079726227711063015095704409550798436788 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

/-- RFC 9496 §A.1: the encoding of `8 B` is
`903293d8f2287ebe10e2374dc1a53e0bc887e592699f02d077d5263cdd55601c`. -/
theorem encodeRep_eight_nsmul_basepoint :
    Ristretto.encodeRep (8 • basepoint) =
      12834969691472587231593312321477678625073638764492513285296224875004126507664 := by
  obtain ⟨hx, hy⟩ := eight_nsmul_basepoint_x_y curve25519.basepoint basepoint_x_eq basepoint_y_eq
  exact encodeRep_of_coords
    (r := 23000972404242694156955020320386166686775676779813540364560723985311582255938) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `9 B` -/

private theorem nine_nsmul_basepoint_x_y (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    (9 • P).x = 24193060302538010417230488029838514081720802923509845138863968807030823940444 ∧
      (9 • P).y = 57551756252899625001155759838357770487605224608455116862194664796369308545472 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

/-- RFC 9496 §A.1: the encoding of `9 B` is
`02622ace8f7303a31cafc63f8fc48fdc16e1c8c8d234b2f0d6685282a9076031`. -/
theorem encodeRep_nine_nsmul_basepoint :
    Ristretto.encodeRep (9 • basepoint) =
      22332999780978691439433262707127500106954015930284539402710831823977601196546 := by
  obtain ⟨hx, hy⟩ := nine_nsmul_basepoint_x_y curve25519.basepoint basepoint_x_eq basepoint_y_eq
  exact encodeRep_of_coords
    (r := 25860964878592866729865149077466376028126010202715821634870612722983097663674) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `10 B` -/

private theorem ten_nsmul_basepoint_x_y (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    (10 • P).x = 43500613248243327786121022071801015118933854441360174117148262713429272820047 ∧
      (10 • P).y = 45005105423099817237495816771148012388779685712352441364231470781391834741548 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

/-- RFC 9496 §A.1: the encoding of `10 B` is
`20706fd788b2720a1ed2a5dad4952b01f413bcf0e7564de8cdc816689e2db95f`. -/
theorem encodeRep_ten_nsmul_basepoint :
    Ristretto.encodeRep (10 • basepoint) =
      43296902171613338270316180077133270930173776004594811824122909877887271137312 := by
  obtain ⟨hx, hy⟩ := ten_nsmul_basepoint_x_y curve25519.basepoint basepoint_x_eq basepoint_y_eq
  exact encodeRep_of_coords
    (r := 23775496168407050728476307448257940900434002109640482907012210020806968671574) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `11 B` -/

private theorem eleven_nsmul_basepoint_x_y (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    (11 • P).x = 9451145793506787353375160377761530931587019091193333050860601958827395183563 ∧
      (11 • P).y = 20609402718286069808115703540855311742885093522056241285814584245966805874451 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

/-- RFC 9496 §A.1: the encoding of `11 B` is
`bce83f8ba5dd2fa572864c24ba1810f9522bc6004afe95877ac73241cafdab42`. -/
theorem encodeRep_eleven_nsmul_basepoint :
    Ristretto.encodeRep (11 • basepoint) =
      30156530449173838445290106302113728740453244852608503736534270739358022625468 := by
  obtain ⟨hx, hy⟩ := eleven_nsmul_basepoint_x_y curve25519.basepoint basepoint_x_eq basepoint_y_eq
  exact encodeRep_of_coords
    (r := 27054922186333675756409881331068898103917418403452157499747384521499367621034) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `12 B` -/

private theorem twelve_nsmul_basepoint_x_y (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    (12 • P).x = 32159939716063394567822525359727347405356413309540137282993608327129696604205 ∧
      (12 • P).y = 29147333543209904737197244325450674102993621692520459538942544703173373584633 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

/-- RFC 9496 §A.1: the encoding of `12 B` is
`e4549ee16b9aa03099ca208c67adafcafa4c3f3e4e5303de6026e3ca8ff84460`. -/
theorem encodeRep_twelve_nsmul_basepoint :
    Ristretto.encodeRep (12 • basepoint) =
      43543894574131407852979279332177882444676506611650446010128826931834072749284 := by
  obtain ⟨hx, hy⟩ := twelve_nsmul_basepoint_x_y curve25519.basepoint basepoint_x_eq basepoint_y_eq
  exact encodeRep_of_coords
    (r := 27446688300725529313969938649410417677737265657747148603308518262233791394068) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `13 B` -/

private theorem thirteen_nsmul_basepoint_x_y (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    (13 • P).x = 7442235066513780790779899786332475485840754593728627195931759107337804079085 ∧
      (13 • P).y = 8529785864514984411577036536286432879603480171865651918962709025066066124672 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

/-- RFC 9496 §A.1: the encoding of `13 B` is
`aa52e000df2e16f55fb1032fc33bc42742dad6bd5a8fc0be0167436c5948501f`. -/
theorem encodeRep_thirteen_nsmul_basepoint :
    Ristretto.encodeRep (13 • basepoint) =
      14163545407837206310051546595701536016361346949044556924887299097062973395626 := by
  obtain ⟨hx, hy⟩ := thirteen_nsmul_basepoint_x_y curve25519.basepoint basepoint_x_eq basepoint_y_eq
  exact encodeRep_of_coords
    (r := 22014132603565178048751708030024053989022926549154153870001412763372316620972) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `14 B` -/

private theorem fourteen_nsmul_basepoint_x_y (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    (14 • P).x = 14642270634066990240227516988620748386040643134865523775420225321890511918521 ∧
      (14 • P).y = 35422008320351900419562335198749713095866812710345432231966142485751234570297 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

/-- RFC 9496 §A.1: the encoding of `14 B` is
`46376b80f409b29dc2b5f6f0c52591990896e5716f41477cd30085ab7f10301e`. -/
theorem encodeRep_fourteen_nsmul_basepoint :
    Ristretto.encodeRep (14 • basepoint) =
      13654307986525245705541547241685942107063914559952375847980265621465556793158 := by
  obtain ⟨hx, hy⟩ := fourteen_nsmul_basepoint_x_y curve25519.basepoint basepoint_x_eq basepoint_y_eq
  exact encodeRep_of_coords
    (r := 15742537566750925888039108908282020821405164932189482342643218283855661233478) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `15 B` -/

private theorem fifteen_nsmul_basepoint_x_y (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    (15 • P).x = 35771902585589234259498423420223840099331465042459337605611172842168536632769 ∧
      (15 • P).y = 8502034780705657720897159939055122322178084209392286764802307224484658961631 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

/-- RFC 9496 §A.1: the encoding of `15 B` is
`e0c418f7c8d9c4cdd7395b93ea124f3ad99021bb681dfc3302a9d99a2e53e64e`. -/
theorem encodeRep_fifteen_nsmul_basepoint :
    Ristretto.encodeRep (15 • basepoint) =
      35687351115805770120198060148188801341203537996309241960823042583481424594144 := by
  obtain ⟨hx, hy⟩ := fifteen_nsmul_basepoint_x_y curve25519.basepoint basepoint_x_eq basepoint_y_eq
  exact encodeRep_of_coords
    (r := 18172309307421360256977488612855814185825149084848020461244509251665279586370) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end curve25519.Proofs
