//============================================================
// SVA checkers for top_module and submodules (concise, high quality)
//============================================================

// Top-level functional/spec checks
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [15:0] A,
  input logic [15:0] B,
  input logic [15:0] Y,
  input logic        select,        // DUT internal
  input logic [15:0] shifted_data   // DUT internal
);

  function automatic logic [15:0] shr_zerofill (input logic [15:0] x, input logic [3:0] s);
    return x >> s;
  endfunction

  // Control must not be X at the sampling edge
  assert property (@(posedge clk) !$isunknown(reset));
  assert property (@(posedge clk) !$isunknown(select));

  // Synchronous reset behavior
  assert property (@(posedge clk) reset |-> (Y == 16'h0));

  // Datapath spec: when not in reset, Y equals selected input logically right-shifted
  let sel_data = select ? B : A;
  let sel_amt  = select ? B[11:8] : A[11:8];
  assert property (@(posedge clk) !reset |-> (Y == shr_zerofill(sel_data, sel_amt)));

  // Internal consistency: shifted_data matches spec each cycle
  assert property (@(posedge clk) !reset |-> (shifted_data == shr_zerofill(sel_data, sel_amt)));

  // Coverage
  cover property (@(posedge clk) reset);
  cover property (@(posedge clk) !reset && (select==0) && (sel_amt==4'd0));
  cover property (@(posedge clk) !reset && (select==1) && (sel_amt==4'd15));
  cover property (@(posedge clk) !reset && $changed(select));

endmodule

// Comparator checks
module comparator_4bit_sva (
  input logic clk,
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       GT
);
  assert property (@(posedge clk) GT == (A > B));
  cover  property (@(posedge clk) GT==1);
  cover  property (@(posedge clk) GT==0);
endmodule

// Barrel shifter checks (spec: logical right shift)
module barrel_shifter_16bit_sva (
  input logic        clk,
  input logic [15:0] A,
  input logic [3:0]  shift_amount,
  input logic [15:0] Y
);
  // Guard against Xs to avoid vacuous failures while still checking logic
  assert property (@(posedge clk) !$isunknown({A,shift_amount}) |-> (Y == (A >> shift_amount)));

  // Spot coverage on key shift amounts
  cover  property (@(posedge clk) (shift_amount==4'd0));
  cover  property (@(posedge clk) (shift_amount==4'd1));
  cover  property (@(posedge clk) (shift_amount==4'd8));
  cover  property (@(posedge clk) (shift_amount==4'd15));
endmodule

// Priority encoder checks (only assert for one-hot inputs)
module priority_encoder_4bit_sva (
  input logic       clk,
  input logic [3:0] A,
  input logic [1:0] Y
);
  let onehot = (A!=4'b0) && ((A & (A-1))==4'b0);
  let enc    = A[0] ? 2'b00 :
               A[1] ? 2'b01 :
               A[2] ? 2'b10 :
               2'b11; // A[3]

  assert property (@(posedge clk) onehot |-> (Y == enc));

  // Coverage for all encoded outputs
  cover  property (@(posedge clk) onehot && (Y==2'b00));
  cover  property (@(posedge clk) onehot && (Y==2'b01));
  cover  property (@(posedge clk) onehot && (Y==2'b10));
  cover  property (@(posedge clk) onehot && (Y==2'b11));
endmodule

//============================================================
// Bind checkers into the DUT
//============================================================
bind top_module           top_module_sva           u_top_sva           (.clk(clk), .reset(reset), .A(A), .B(B), .Y(Y), .select(select), .shifted_data(shifted_data));
bind comparator_4bit      comparator_4bit_sva      u_cmp_sva            (.clk(top_module.clk), .A(A), .B(B), .GT(GT));
bind barrel_shifter_16bit barrel_shifter_16bit_sva u_shf_sva            (.clk(top_module.clk), .A(A), .shift_amount(shift_amount), .Y(Y));
bind priority_encoder_4bit priority_encoder_4bit_sva u_enc_sva          (.clk(top_module.clk), .A(A), .Y(Y));