// SVA for magnitude_comparator_selector_decoder
module magnitude_comparator_selector_decoder_sva (
  input  logic        clk,
  input  logic [2:0]  a, b,
  input  logic [1:0]  select,
  input  logic [2:0]  magnitude_result,
  input  logic [2:0]  a_mag,
  input  logic [2:0]  b_mag,
  input  logic [2:0]  comparison_result,
  input  logic [1:0]  input_selected,
  input  logic        Y0, Y1, Y2, Y3,
  input  logic [1:0]  final_output
);

  default clocking cb @(posedge clk); endclocking

  // Past-valid helper (skip first cycle checks that need it)
  logic past1;
  always_ff @(posedge clk) past1 <= 1'b1;

  // Magnitude comparator stage (a,b -> magnitude_result,a_mag,b_mag)
  assert property ( (a > b) |=> magnitude_result == 3'b001 );
  assert property ( (a < b) |=> magnitude_result == 3'b010 );
  assert property ( (a == b) |=> magnitude_result == 3'b100 );

  assert property ( (a > b) |=> (a_mag == $past(a) && b_mag == 3'b000) );
  assert property ( (a < b) |=> (a_mag == 3'b000 && b_mag == $past(b)) );
  assert property ( (a == b) |=> (a_mag == 3'b000 && b_mag == 3'b000) );

  // Encoding sanity
  assert property ( past1 |-> $onehot(magnitude_result) ); // 001/010/100 only

  // Selector stage (select,magnitude_result -> comparison_result,input_selected)
  assert property ( (select == 2'b00) |=> (comparison_result == $past(magnitude_result) && input_selected == 2'b00) );
  assert property ( (select == 2'b01) |=> (comparison_result == $past(magnitude_result) && input_selected == 2'b01) );
  assert property ( (select == 2'b10) |=> (comparison_result == 3'b000              && input_selected == 2'b00) );
  assert property ( (select == 2'b11) |=> (comparison_result == 3'b000              && input_selected == 2'b01) );

  // Selector encoding sanity: allow one-hot or zero
  assert property ( past1 |-> $onehot0(comparison_result) );

  // Decoder stage (comparison_result -> Y[3:0])
  assert property ( (comparison_result == 3'b001) |=> ( Y3 && !Y2 && !Y1 && !Y0 ) );
  assert property ( (comparison_result == 3'b010) |=> ( !Y3 && Y2 && !Y1 && !Y0 ) );
  assert property ( (comparison_result == 3'b100) |=> ( !Y3 && !Y2 && Y1 && !Y0 ) );
  assert property ( (comparison_result == 3'b000) |=> ( !Y3 && !Y2 && !Y1 && Y0 ) );
  // One-hot sanity on decoder outputs
  assert property ( past1 |-> $onehot({Y3,Y2,Y1,Y0}) );

  // Final output stage (Y -> final_output)
  assert property ( past1 |-> final_output == {$past(Y3), $past(Y2)} );
  assert property ( past1 |-> final_output != 2'b11 );

  // Cross-stage quick path checks for force-to-zero select
  assert property ( (select[1] == 1'b1) |=> (comparison_result == 3'b000) ##1 (Y0 && !Y1 && !Y2 && !Y3) );

  // Functional coverage
  cover property ( a > b );
  cover property ( a < b );
  cover property ( a == b );

  cover property ( select == 2'b00 );
  cover property ( select == 2'b01 );
  cover property ( select == 2'b10 );
  cover property ( select == 2'b11 );

  cover property ( comparison_result == 3'b001 );
  cover property ( comparison_result == 3'b010 );
  cover property ( comparison_result == 3'b100 );
  cover property ( comparison_result == 3'b000 );

  cover property ( Y3 ); // a>b path observed at decoder
  cover property ( Y2 ); // a<b path observed at decoder
  cover property ( Y1 ); // a==b path observed at decoder
  cover property ( Y0 ); // forced-zero/default path observed at decoder

  cover property ( final_output == 2'b10 ); // came from Y3
  cover property ( final_output == 2'b01 ); // came from Y2
  cover property ( final_output == 2'b00 ); // came from Y1 or Y0

  // End-to-end illustrative covers through pipeline
  cover property ( (a>b) ##1 (select[1]==0) ##1 (comparison_result==3'b001) ##1 Y3 ##1 (final_output==2'b10) );
  cover property ( (a<b) ##1 (select[1]==0) ##1 (comparison_result==3'b010) ##1 Y2 ##1 (final_output==2'b01) );
  cover property ( (a==b) ##1 (select[1]==0) ##1 (comparison_result==3'b100) ##1 Y1 ##1 (final_output==2'b00) );
  cover property ( (select[1]==1) ##1 (comparison_result==3'b000) ##1 Y0 ##1 (final_output==2'b00) );

endmodule

// Bind example:
// bind magnitude_comparator_selector_decoder magnitude_comparator_selector_decoder_sva sva (
//   .clk(clk), .a(a), .b(b), .select(select),
//   .magnitude_result(magnitude_result), .a_mag(a_mag), .b_mag(b_mag),
//   .comparison_result(comparison_result), .input_selected(input_selected),
//   .Y0(Y0), .Y1(Y1), .Y2(Y2), .Y3(Y3), .final_output(final_output)
// );