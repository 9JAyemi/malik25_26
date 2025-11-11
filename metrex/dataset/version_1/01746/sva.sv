// SVA checker for alu. Bind this to the DUT.
// Concise, high-quality functional equivalence checks plus key coverage.

module alu_sva_checker (
  input  logic [63:0] inA_i,
  input  logic [63:0] inB_i,
  input  logic        cflag_i,
  input  logic        sum_en_i,
  input  logic        and_en_i,
  input  logic        xor_en_i,
  input  logic        invB_en_i,
  input  logic        lsh_en_i,
  input  logic        rsh_en_i,
  input  logic        ltu_en_i,
  input  logic        lts_en_i,
  input  logic [63:0] out_o,
  input  logic        cflag_o,
  input  logic        vflag_o,
  input  logic        zflag_o
);
  default clocking cb @(*); endclocking

  // Reference model (pure combinational)
  logic [63:0] b_ref;
  logic [64:0] full_sum_ref;
  logic [63:0] rawSums_ref, sums_ref, ands_ref, xors_ref;
  logic [63:0] lsh_ref, rsh_ref;
  logic [63:0] isLTS_ref, isLTU_ref, out_ref;
  logic        cflag_ref, vflag_ref;

  assign b_ref         = inB_i ^ {64{invB_en_i}};
  assign full_sum_ref  = {1'b0,inA_i} + {1'b0,b_ref} + cflag_i;
  assign rawSums_ref   = full_sum_ref[63:0];
  assign cflag_ref     = full_sum_ref[64];
  assign vflag_ref     = (inA_i[63] ~^ b_ref[63]) & (rawSums_ref[63] ^ inA_i[63]);
  assign sums_ref      = sum_en_i ? rawSums_ref : 64'd0;
  assign ands_ref      = and_en_i ? (inA_i & b_ref) : 64'd0;
  assign xors_ref      = xor_en_i ? (inA_i ^ b_ref) : 64'd0;
  assign lsh_ref       = lsh_en_i ? (inA_i <<  inB_i[5:0]) : 64'd0;
  assign rsh_ref       = rsh_en_i ? (cflag_i ? $signed(inA_i) >>> inB_i[5:0]
                                            :  inA_i >>          inB_i[5:0]) : 64'd0;
  assign isLTS_ref     = lts_en_i ? {63'd0, rawSums_ref[63] ^ vflag_ref} : 64'd0;
  assign isLTU_ref     = ltu_en_i ? {63'd0, ~cflag_ref} : 64'd0;
  assign out_ref       = sums_ref | ands_ref | xors_ref | lsh_ref | rsh_ref | isLTS_ref | isLTU_ref;

  // X-prop sanity: known inputs imply known outputs
  assert property ( !$isunknown({inA_i,inB_i,cflag_i,sum_en_i,and_en_i,xor_en_i,invB_en_i,lsh_en_i,rsh_en_i,ltu_en_i,lts_en_i})
                    |-> !$isunknown({out_o,cflag_o,vflag_o,zflag_o}) );

  // Core functional equivalence
  assert property ( out_o   == out_ref );
  assert property ( cflag_o == cflag_ref );
  assert property ( vflag_o == vflag_ref );
  assert property ( zflag_o == (out_o == 64'd0) );

  // Per-op isolation checks (when only one op is enabled)
  assert property ( sum_en_i && !(and_en_i|xor_en_i|lsh_en_i|rsh_en_i|ltu_en_i|lts_en_i)
                    |-> out_o == rawSums_ref );
  assert property ( and_en_i && !(sum_en_i|xor_en_i|lsh_en_i|rsh_en_i|ltu_en_i|lts_en_i)
                    |-> out_o == (inA_i & b_ref) );
  assert property ( xor_en_i && !(sum_en_i|and_en_i|lsh_en_i|rsh_en_i|ltu_en_i|lts_en_i)
                    |-> out_o == (inA_i ^ b_ref) );
  assert property ( lsh_en_i && !(sum_en_i|and_en_i|xor_en_i|rsh_en_i|ltu_en_i|lts_en_i)
                    |-> out_o == (inA_i << inB_i[5:0]) );
  assert property ( rsh_en_i && !(sum_en_i|and_en_i|xor_en_i|lsh_en_i|ltu_en_i|lts_en_i)
                    |-> out_o == (cflag_i ? $signed(inA_i) >>> inB_i[5:0] : inA_i >> inB_i[5:0]) );
  assert property ( lts_en_i && !(sum_en_i|and_en_i|xor_en_i|lsh_en_i|rsh_en_i|ltu_en_i)
                    |-> out_o[0] == (rawSums_ref[63] ^ vflag_ref) && out_o[63:1]==63'd0 );
  assert property ( ltu_en_i && !(sum_en_i|and_en_i|xor_en_i|lsh_en_i|rsh_en_i|lts_en_i)
                    |-> out_o[0] == ~cflag_ref && out_o[63:1]==63'd0 );

  // Targeted shifter details (spot checks)
  assert property ( rsh_en_i && cflag_i && (inB_i[5:0]!=0)
                    |-> out_o[63] == inA_i[63] ); // arithmetic fill
  assert property ( rsh_en_i && !cflag_i && (inB_i[5:0]!=0)
                    |-> out_o[63] == 1'b0 );      // logical fill

  // Coverage: exercise each op and key corner cases
  cover property ( invB_en_i==0 );
  cover property ( invB_en_i==1 );

  cover property ( sum_en_i && (cflag_ref==1) );
  cover property ( sum_en_i && (vflag_ref==1) );
  cover property ( sum_en_i && (rawSums_ref==64'd0) );

  cover property ( and_en_i );
  cover property ( xor_en_i );

  cover property ( lsh_en_i && (inB_i[5:0]==6'd0) );
  cover property ( lsh_en_i && (inB_i[5:0]==6'd1) );
  cover property ( lsh_en_i && (inB_i[5:0]==6'd32) );
  cover property ( lsh_en_i && (inB_i[5:0]==6'd63) );

  cover property ( rsh_en_i && !cflag_i && (inB_i[5:0]==6'd31) );
  cover property ( rsh_en_i &&  cflag_i && (inB_i[5:0]==6'd63) && inA_i[63] );

  cover property ( lts_en_i && (out_ref[0]==1) );
  cover property ( ltu_en_i && (out_ref[0]==1) );

  cover property ( zflag_o==1 );
  cover property ( zflag_o==0 );

  // Coverage: overlapping enables (ensure OR-path is exercised)
  cover property ( (sum_en_i + and_en_i + xor_en_i + lsh_en_i + rsh_en_i + ltu_en_i + lts_en_i) >= 2 );

endmodule

bind alu alu_sva_checker alu_sva_checker_i(.*);