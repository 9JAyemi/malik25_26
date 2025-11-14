// SVA for top_module
// Bindable, concise, with functional checks and targeted coverage

module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic [31:0] data_in,
  input  logic [4:0]  shift_amt,
  input  logic        select,
  input  logic [31:0] result,
  input  logic [3:0]  adder_out,      // top_module.adder_out
  input  logic [31:0] shifted_out     // top_module.shifted_out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reference models
  function automatic [31:0] shifter_ref (input [31:0] d, input [4:0] s);
    shifter_ref = s[4] ? {32{d[31]}} :
                  s[3] ? {d[31], d[31:1]} :
                  s[2] ? {d[31:2], d[1:0]} :
                  s[1] ? {d[31:3], d[2:0]} :
                         {d[31:4], d[3:0]};
  endfunction

  function automatic [31:0] mux_ref (input bit sel, input [3:0] sum4, input [31:0] sh32);
    mux_ref = sel ? sh32 : {28'b0, sum4};
  endfunction

  // Ripple-carry adder: functional and reset checks
  assert property (reset |-> adder_out == 4'h0);
  assert property (@(posedge reset) adder_out == 4'h0);

  // Check last-cycle value to avoid sampling races:
  // value held in adder_out in the previous cycle equals A+B of that same previous cycle
  assert property ( $past(!reset) |-> $past(adder_out) == ($past(A)+$past(B)) [3:0] );

  // Adder output must not glitch between clocks
  assert property (@(negedge clk) $stable(adder_out));

  // Barrel shifter correctness (priority behavior as coded)
  assert property ( shifted_out == shifter_ref(data_in, shift_amt) );

  // Top-level mux correctness + zero-extension in add mode
  assert property ( result == mux_ref(select, adder_out, shifted_out) );
  assert property ( !select |-> (result[31:4] == 28'h0 && result[3:0] == adder_out) );

  // Known-ness when inputs are known
  assert property ( !select |-> !$isunknown({A,B,adder_out,result}) );
  assert property (  select |-> !$isunknown({data_in,shift_amt,shifted_out,result}) );

  // Coverage
  cover property (!reset && select==0);
  cover property (!reset && select==1);
  cover property (!reset && shift_amt[4]);
  cover property (!reset && shift_amt[3] && !shift_amt[4]);
  cover property (!reset && shift_amt[2] && !shift_amt[4] && !shift_amt[3]);
  cover property (!reset && shift_amt[1] && !shift_amt[4] && !shift_amt[3] && !shift_amt[2]);
  cover property (!reset && !(|shift_amt[4:1])); // default branch
  cover property (!reset && (A+B) > 4'hF);       // adder overflow/wrap event

endmodule

bind top_module top_module_sva sva_i (
  .clk(clk),
  .reset(reset),
  .A(A),
  .B(B),
  .data_in(data_in),
  .shift_amt(shift_amt),
  .select(select),
  .result(result),
  .adder_out(adder_out),
  .shifted_out(shifted_out)
);