// SVA for two_bit_encoder
module two_bit_encoder_sva(input logic [1:0] data, input logic q, input logic zero);

  // Sample on any input bit change
  default clocking cb @(posedge data[0] or negedge data[0] or posedge data[1] or negedge data[1]); endclocking

  // Functional correctness when inputs are known
  assert property (!$isunknown(data) |=> (q == ~data[0]) && (zero == ~(data[0] | data[1])));

  // Strong equivalences
  assert property (data == 2'b00 |=> (zero && q));      // 00 -> zero=1, q=1
  assert property (zero |-> data == 2'b00);             // zero high iff data==00

  // X-tolerant implication: any '1' on input forces zero low
  assert property ((data[0] === 1'b1 || data[1] === 1'b1) |=> zero === 1'b0);

  // Functional input/output coverage (all 4 combinations)
  cover property (data == 2'b00 &&  q &&  zero);
  cover property (data == 2'b01 && !q && !zero);
  cover property (data == 2'b10 &&  q && !zero);
  cover property (data == 2'b11 && !q && !zero);

  // Output toggle coverage
  cover property ( q ##1 !q);
  cover property (!q ##1  q);
  cover property ( zero ##1 !zero);
  cover property (!zero ##1  zero);

endmodule

bind two_bit_encoder two_bit_encoder_sva sva (.data(data), .q(q), .zero(zero));