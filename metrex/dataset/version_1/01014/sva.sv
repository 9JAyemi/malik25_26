// Bind these assertions to the DUT
bind multiplier_4bit multiplier_4bit_sva m4_sva (.*);

module multiplier_4bit_sva (
  input logic        clk,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic [7:0]  S,
  input logic [3:0]  addr1,
  input logic [3:0]  addr2,
  input logic [7:0]  data1,
  input logic [7:0]  data2,
  input logic [15:0] result,
  input      [7:0]  reg_file [0:15]
);

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Sanity: addresses and S are never X/Z once pipeline starts
  assert property (!$isunknown({addr1,addr2})));
  assert property (!$isunknown(S)));

  // Fetch: addr regs reflect previous cycle inputs
  assert property (addr1 == $past(A));
  assert property (addr2 == $past(B));

  // Execute reads: data regs capture reg_file at previous-cycle addresses
  assert property (data1 == $past(reg_file[$past(addr1)]));
  assert property (data2 == $past(reg_file[$past(addr2)]));

  // Multiply: result is product of prior-cycle operands
  assert property (result == $past(data1) * $past(data2));

  // Writeback: correct bytes written to correct addresses (distinct and equal cases)
  assert property ( ($past(addr1) != $past(addr2))
                    |-> (reg_file[$past(addr1)] == $past(result[7:0])
                         && reg_file[$past(addr2)] == $past(result[15:8])) );

  assert property ( ($past(addr1) == $past(addr2))
                    |-> (reg_file[$past(addr1)] == $past(result[15:8])) );

  // No unintended writes: all other reg_file entries remain stable
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_no_spurious
      assert property ( (i != $past(addr1) && i != $past(addr2))
                        |-> reg_file[i] == $past(reg_file[i]) );
    end
  endgenerate

  // Output mapping: S always mirrors reg_file at current addr1
  assert property (S == reg_file[addr1]);

  // Output reflects latest write when indexing matches last cycle's write address
  // - Low-byte case (distinct addresses)
  assert property ( (addr1 == $past(addr1) && $past(addr1) != $past(addr2))
                    |-> S == $past(result[7:0]) );
  // - High-byte overwrite case (same addresses)
  assert property ( (addr1 == $past(addr1) && $past(addr1) == $past(addr2))
                    |-> S == $past(result[15:8]) );

  // Functional coverage
  cover property ($past(addr1) != $past(addr2));  // distinct write addresses
  cover property ($past(addr1) == $past(addr2));  // same-address overwrite
  cover property (addr1 == $past(addr1) && $past(addr1) != $past(addr2) && S == $past(result[7:0]));
  cover property (addr1 == $past(addr1) && $past(addr1) == $past(addr2) && S == $past(result[15:8]));
  cover property (result != 16'h0);
  cover property (result == 16'h0);

  // Each register gets written at least once
  generate
    for (i = 0; i < 16; i++) begin : g_cover_written
      cover property (reg_file[i] != $past(reg_file[i]));
    end
  endgenerate

endmodule