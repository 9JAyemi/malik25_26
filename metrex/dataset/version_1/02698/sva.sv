// SVA for top_module and barrel_shifter (concise, combinational sampling)

module top_module_sva (
  input  logic [3:0] A,
  input  logic [1:0] shift_type,
  input  logic       select,
  input  logic [3:0] B
);
  // Create a combinational sampling event
  event comb_ev; always @* -> comb_ev;

  // Reference functions for expected behavior
  function automatic logic [3:0] sll1 (input logic [3:0] x); sll1 = {x[2:0],1'b0}; endfunction
  function automatic logic [3:0] srl1 (input logic [3:0] x); srl1 = {1'b0,x[3:1]}; endfunction
  function automatic logic [3:0] asl_spec (input logic [3:0] x); asl_spec = {x[2],x[3],x[3],x[3]}; endfunction
  function automatic logic [3:0] asr_spec (input logic [3:0] x); asr_spec = {x[0],x[0],x[0],x[1]}; endfunction
  function automatic logic [3:0] shifter_out (input logic [3:0] x, input logic [1:0] t);
    case (t)
      2'b00: shifter_out = sll1(x);
      2'b01: shifter_out = srl1(x);
      2'b10: shifter_out = asl_spec(x);
      default: shifter_out = asr_spec(x);
    endcase
  endfunction

  // Core functional check (covers select path, multiply by 3 truncated to 4b, and all shift types)
  assert property (@(comb_ev) B == (select ? shifter_out(A,shift_type) : (A*3)[3:0]));

  // No-X check: clean inputs imply clean output
  assert property (@(comb_ev) !$isunknown({A,shift_type,select}) |-> !$isunknown(B));

  // Combinational stability: stable inputs imply stable output
  assert property (@(comb_ev) $stable({A,shift_type,select}) |-> $stable(B));

  // Coverage
  cover property (@(comb_ev) !select);                      // multiply path exercised
  cover property (@(comb_ev)  select);                      // shift path exercised
  cover property (@(comb_ev)  select && shift_type==2'b00);
  cover property (@(comb_ev)  select && shift_type==2'b01);
  cover property (@(comb_ev)  select && shift_type==2'b10);
  cover property (@(comb_ev)  select && shift_type==2'b11);
  cover property (@(comb_ev) !select && (A*3)>=16);         // multiply overflow/truncation
  cover property (@(comb_ev)  select && shift_type==2'b00 && A[3]); // left shift drops MSB
  cover property (@(comb_ev)  select && shift_type==2'b01 && A[0]); // right shift drops LSB
  cover property (@(comb_ev) $rose(select));
  cover property (@(comb_ev) $fell(select));
endmodule

bind top_module top_module_sva u_top_sva(.A(A), .shift_type(shift_type), .select(select), .B(B));


// SVA for barrel_shifter itself
module barrel_shifter_sva (
  input  logic [3:0] in,
  input  logic [1:0] shift_type,
  input  logic [3:0] out
);
  event comb_ev; always @* -> comb_ev;

  function automatic logic [3:0] sll1 (input logic [3:0] x); sll1 = {x[2:0],1'b0}; endfunction
  function automatic logic [3:0] srl1 (input logic [3:0] x); srl1 = {1'b0,x[3:1]}; endfunction
  function automatic logic [3:0] asl_spec (input logic [3:0] x); asl_spec = {x[2],x[3],x[3],x[3]}; endfunction
  function automatic logic [3:0] asr_spec (input logic [3:0] x); asr_spec = {x[0],x[0],x[0],x[1]}; endfunction
  function automatic logic [3:0] shifter_out (input logic [3:0] x, input logic [1:0] t);
    case (t)
      2'b00: shifter_out = sll1(x);
      2'b01: shifter_out = srl1(x);
      2'b10: shifter_out = asl_spec(x);
      default: shifter_out = asr_spec(x);
    endcase
  endfunction

  // Exact functional mapping
  assert property (@(comb_ev) out == shifter_out(in,shift_type));

  // No-X propagation from clean inputs
  assert property (@(comb_ev) !$isunknown({in,shift_type}) |-> !$isunknown(out));

  // Coverage of all shift modes
  cover property (@(comb_ev) shift_type==2'b00);
  cover property (@(comb_ev) shift_type==2'b01);
  cover property (@(comb_ev) shift_type==2'b10);
  cover property (@(comb_ev) shift_type==2'b11);
endmodule

bind barrel_shifter barrel_shifter_sva u_bs_sva(.in(in), .shift_type(shift_type), .out(out));