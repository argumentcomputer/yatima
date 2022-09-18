import Lean

namespace Yatima.Ipld

inductive PrimConst
  | nat | natZero | natSucc | string

open Std (RBMap) in
def primCidsMap : RBMap String PrimConst compare := .ofList [
  ("bagcyb6egbqlcbvcn3yk3eojuobxafm2yn42oyux6im7vkcwrx7zykci56kwbt6pm", .nat),
  ("bagcyb6egbqlcbtdf56fiqql3sk3ei2nt4zwsudg4z5tcdehqqvrw4duozqjbp4ao", .natZero),
  ("bagcyb6egbqlcbop4tscfzg2s3eb7cfprycbn2r2oufqqmcg4uf5vcsqcp75fkeuh", .natSucc),
  ("bagcyb6egbqlcba4ftu73ay23wjzrrrf5t3uycgkjftlubwgakbty2k4t4jer5ydf", .string)
]

end Yatima.Ipld
