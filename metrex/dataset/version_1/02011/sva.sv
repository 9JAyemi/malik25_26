// SVA for adder_subtractor_4bit
// Bind this module to the DUT. Example:
// bind adder_subtractor_4bit adder_subtractor_4bit_sva
//   #(.CHECK_SUB_INTENT(1)) u_sva ( .clk(tb.clk), .rst_n(tb.rst_n),
//     .A(A), .B(B), .SUB(SUB), .SUM(SUM), .CIN(CIN), .COUT(COUT) );

module adder_subtractor_4bit_sva
  #(parameter bit CHECK_SUB_INTENT = 1)
  (input  logic        clk,
   input  logic        rst_n,
   input  logic [3:0]  A,
   input  logic [3:0]  B,
   input  logic        SUB,
   input  logic [3:0]  SUM,
   input  logic [3:0]  CIN,
   input  logic [3:0]  COUT);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Sanity/X check
  ap_no_x_leak: assert property ($isunknown({A,B,SUB}) |-> $isunknown({SUM,COUT}));

  // Carry-chain wiring must match spec
  ap_chain: assert property (CIN[0]==SUB && CIN[1]==COUT[0] && CIN[2]==COUT[1] && CIN[3]==COUT[2]);

  // Per-bit correctness (matches a full-adder truth table)
  ap_b0: assert property ( {COUT[0], SUM[0]} == {1'b0,A[0]} + {1'b0,B[0]} + CIN[0] );
  genvar i;
  generate
    for (i=1;i<4;i++) begin : g_bit
      ap_b: assert property ( {COUT[i], SUM[i]} == {1'b0,A[i]} + {1'b0,B[i]} + COUT[i-1] );
    end
  endgenerate

  // End-to-end arithmetic must equal A + B + SUB (5-bit)
  ap_e2e_add: assert property ( {COUT[3], SUM} == {1'b0,A} + {1'b0,B} + SUB );

  // Mode checks
  ap_add_mode: assert property ( !SUB |-> (SUM == (A + B)) );
  if (CHECK_SUB_INTENT) begin : g_sub_intent
    // Intended subtract behavior (will flag if design misses B^SUB)
    ap_sub_mode_intent: assert property ( SUB |-> (SUM == (A + ~B + 4'd1)) );
  end

  // Functional coverage (concise but meaningful)
  cp_seen_add:   cover property (!SUB);
  cp_seen_sub:   cover property ( SUB);

  // Carry scenarios
  cp_no_carry:   cover property (!SUB && (COUT == 4'b0000));
  cp_full_chain: cover property ( SUB && (&COUT));          // all carries ripple
  cp_msb_carry:  cover property ( COUT[3]);                 // overflow from MSB

  // Subtract intent example (A<B) should produce borrow result (mod 16)
  cp_sub_borrow: cover property ( SUB && (A < B) && (SUM == (A + ~B + 4'd1)) );

endmodule