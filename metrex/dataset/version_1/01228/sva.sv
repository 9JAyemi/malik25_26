// SVA bind module for Alu
module Alu_sva #(parameter wrd_size = 8, sel_width = 3)
(
  input  logic [wrd_size-1:0] Alu_in1,
  input  logic [wrd_size-1:0] Alu_in2,
  input  logic [sel_width-1:0] Alu_sel,
  input  logic [wrd_size-1:0] Alu_out,
  input  logic                Alu_zero_flg
);

  localparam NOP = 3'b000,
             ADD = 3'b001,
             SUB = 3'b010,
             AND = 3'b011,
             OR  = 3'b100,
             SLT = 3'b101,
             SRT = 3'b110,
             NOT = 3'b111;

  // Event for combinational sampling
  event comb_ev;
  always @ (Alu_in1 or Alu_in2 or Alu_sel or Alu_out or Alu_zero_flg) -> comb_ev;

  function automatic bit clean_in();
    return !$isunknown({Alu_in1, Alu_in2, Alu_sel});
  endfunction
  function automatic bit clean_all();
    return !$isunknown({Alu_in1, Alu_in2, Alu_sel, Alu_out, Alu_zero_flg});
  endfunction

  // Outputs known when inputs known
  assert property (@(comb_ev) clean_in() |-> !$isunknown({Alu_out, Alu_zero_flg}));

  // Sel must be one of defined ops (with known inputs)
  assert property (@(comb_ev) clean_in() |-> (Alu_sel inside {NOP,ADD,SUB,AND,OR,SLT,SRT,NOT}));

  // Zero flag correctness
  assert property (@(comb_ev) !$isunknown(Alu_out) |-> (Alu_zero_flg == ~|Alu_out));

  // Functional correctness per opcode
  assert property (@(comb_ev) clean_in() && (Alu_sel==NOP) |-> (Alu_out == '0));
  assert property (@(comb_ev) clean_in() && (Alu_sel==AND) |-> (Alu_out == (Alu_in1 & Alu_in2)));
  assert property (@(comb_ev) clean_in() && (Alu_sel==OR ) |-> (Alu_out == (Alu_in1 | Alu_in2)));
  assert property (@(comb_ev) clean_in() && (Alu_sel==ADD) |-> (Alu_out == (Alu_in1 + Alu_in2)));
  assert property (@(comb_ev) clean_in() && (Alu_sel==SUB) |-> (Alu_out == (Alu_in1 - Alu_in2)));
  assert property (@(comb_ev) clean_in() && (Alu_sel==NOT) |-> (Alu_out == ~Alu_in1));
  assert property (@(comb_ev) clean_in() && (Alu_sel==SLT) |-> (Alu_out == (Alu_in1 << Alu_in2)));
  assert property (@(comb_ev) clean_in() && (Alu_sel==SRT) |-> (Alu_out == (Alu_in1 >> Alu_in2)));

  // Minimal functional coverage
  cover property (@(comb_ev) clean_all() && (Alu_sel==NOP));
  cover property (@(comb_ev) clean_all() && (Alu_sel==AND));
  cover property (@(comb_ev) clean_all() && (Alu_sel==OR ));
  cover property (@(comb_ev) clean_all() && (Alu_sel==ADD));
  cover property (@(comb_ev) clean_all() && (Alu_sel==SUB));
  cover property (@(comb_ev) clean_all() && (Alu_sel==NOT));
  cover property (@(comb_ev) clean_all() && (Alu_sel==SLT));
  cover property (@(comb_ev) clean_all() && (Alu_sel==SRT));

  // Zero flag observed both ways
  cover property (@(comb_ev) clean_all() && (Alu_zero_flg==1'b1));
  cover property (@(comb_ev) clean_all() && (Alu_zero_flg==1'b0));

  // Interesting corner cases
  cover property (@(comb_ev) clean_all() && (Alu_sel==ADD) && ((Alu_in1 + Alu_in2) < Alu_in1)); // unsigned overflow
  cover property (@(comb_ev) clean_all() && (Alu_sel==SUB) && (Alu_in1 < Alu_in2));            // unsigned borrow
  cover property (@(comb_ev) clean_all() && (Alu_sel==SLT) && ($unsigned(Alu_in2)==0));
  cover property (@(comb_ev) clean_all() && (Alu_sel==SLT) && ($unsigned(Alu_in2) >= wrd_size));
  cover property (@(comb_ev) clean_all() && (Alu_sel==SRT) && ($unsigned(Alu_in2)==0));
  cover property (@(comb_ev) clean_all() && (Alu_sel==SRT) && ($unsigned(Alu_in2) >= wrd_size));

endmodule

// Bind into DUT
bind Alu Alu_sva #(.wrd_size(wrd_size), .sel_width(sel_width)) i_Alu_sva
(
  .Alu_in1(Alu_in1),
  .Alu_in2(Alu_in2),
  .Alu_sel(Alu_sel),
  .Alu_out(Alu_out),
  .Alu_zero_flg(Alu_zero_flg)
);