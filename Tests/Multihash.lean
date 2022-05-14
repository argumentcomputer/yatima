import Yatima.YatimaSpec
import Yatima.Ipld.Multihash

structure Case where
  input: ByteArray
  hash: Multihash

/-- Test that a given test-case passes -/
def testCase (case : Case) : Bool := 
  let hash := Multihash.sha3_512 case.input
  hash == case.hash &&
  Multihash.fromBytes (Multihash.toBytes hash) == some hash

def findFailing (cases: List Case) : List Case :=
  List.filter (fun x => not (testCase x)) cases

def mkCase (input: String) (hash: String) : Option Case := do
  let input ← input.toUTF8
  let hash  ← ByteArray.mk <$> Array.mk <$> Multibase.decode Multibase.Base16 hash
  let hash  ← Multihash.fromBytes hash
  return Case.mk input hash

def cases : List Case := List.catOptions
  [ mkCase "431fb5d4c9b735ba1a34d0df045118806ae2336f2c" "f14409a7a8207a57d03e9c524ae7fd39563bfe1a466a3a0323875eba8b034a1d59c3b7218103543f7777f17ef03dcaf44d12c74dfb83726e7425cf61225e9a54b3b3a"
  , mkCase "2d6db2d7882fa8b7d56e74b8e24036deb475de8c94" "f1440968e697b2d5e92470002f9e59e13557f47b895dc9c79082a90e91515f025563773aec0f70219c87350c79707de67500866d7fe084c5316e12c6930949b28865d"
  , mkCase "6c00022ba29d15926c4580332ded091e666f0ec5d9" "f144047f57e2056010afa03bc58141ba3754f41917518c81711236eaca3766e333b9a2a767a90363f7a179e776d85aa6610713709ee46531f9a454565f737c68bdc56"
  , mkCase "1391551dc8f15110d256c493ed485bca8cfed07241" "f144089c62811bc2d3fec81631112ad9f03de23d065697f758b8df9e5d791474ab2f20ddac684c23b203b730be465a5d0f06b76e9dbc48590def7d58e96d93b4e0418"
  , mkCase "557f47c855a5ca40daa3c0904a1e43647b4021ce0c" "f1440a7ab209784597d2e251860e2464c04c386c4887af778136414c80d7c643ccd3b2a0b61e31986a79ef8e4fdd41601fbe7c982c132df4bc77ecc2e27d3edd55f90"
  , mkCase "4c44254356730838195a32cbb1b8be3bed4c6c05c0" "f14403dc43b479f5e9e008a5256ca442e66286995c39deb732a6fb4e2e791a3c4a6a6e5322e571e945a78748896edc67866ab00c767320f6956833857eab991a73a77"
  ]

test_suite
  it "decodes multihashes" so findFailing cases should be empty