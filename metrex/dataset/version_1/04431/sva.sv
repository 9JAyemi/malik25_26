// SVA for mult12_8
module mult12_8_sva (
  input logic        clock,
  input logic [11:0] dataa,
  input logic [7:0]  datab,
  input logic [19:0] result
);

  default clocking cb @ (posedge clock); endclocking

  // Knownness
  a_inputs_known:  assert property ( !$isunknown({dataa, datab}) );
  a_result_known:  assert property ( 1'b1 |=> !$isunknown(result) );

  // Functional equivalence: result == ((dataa*datab) << 8)[19:0]
  property p_core_fn;
    logic [19:0] prod;
    (prod = (dataa * datab), 1) |=> (result == ((prod << 8) & 20'hFFFFF));
  endproperty
  a_core_fn: assert property (p_core_fn);

  // Bit-level consequences
  a_lsb_zero:  assert property ( 1'b1 |=> (result[7:0]  == 8'h00) );
  property p_low12_pass;
    logic [19:0] prod;
    (prod = (dataa * datab), 1) |=> (result[19:8] == prod[11:0]);
  endproperty
  a_low12_pass: assert property (p_low12_pass);

  // Sanity cases
  a_zero_mult:   assert property ( ((dataa==12'h000) || (datab==8'h00)) |=> (result==20'h00000) );
  a_mult_by_one: assert property ( (datab==8'h01) |=> (result == {dataa,8'h00}) );

  // Coverage
  cover_zero_a:     cover property ( (dataa==12'h000) && (datab!=8'h00) );
  cover_zero_b:     cover property ( (datab==8'h00) && (dataa!=12'h000) );
  cover_nonzero:    cover property ( (dataa!=12'h000) && (datab!=8'h00) );
  cover_max:        cover property ( (dataa==12'hFFF) && (datab==8'hFF) );
  cover_by_one:     cover property ( (datab==8'h01) );
  // Truncation/overflow of high 8 bits of the 20-bit product
  property p_overflow_trunc;
    logic [19:0] prod;
    (prod = (dataa * datab)) ##0 (prod[19:12] != 8'h00);
  endproperty
  cover_overflow_trunc: cover property (p_overflow_trunc);

endmodule

// Bind into DUT
bind mult12_8 mult12_8_sva sva_i (
  .clock (clock),
  .dataa (dataa),
  .datab (datab),
  .result(result)
);