// SVA for EHRU_6: concise, high-quality checks and coverage
// Bind example (place in a package or a separate .sv file):
// bind EHRU_6 EHRU_6_sva #(.DATA_SZ(DATA_SZ)) sva (.*);

module EHRU_6_sva #(parameter DATA_SZ = 1)
(
  input logic                CLK,
  input logic [DATA_SZ-1:0]  read_0, read_1, read_2, read_3, read_4, read_5,
  input logic [DATA_SZ-1:0]  write_0, write_1, write_2, write_3, write_4, write_5,
  input logic                EN_write_0, EN_write_1, EN_write_2,
                             EN_write_3, EN_write_4, EN_write_5
);
  default clocking cb @(posedge CLK); endclocking

  // Sanity: no X/Z on key controls/data/outputs at sampling edge
  assert property (!$isunknown({
    EN_write_0,EN_write_1,EN_write_2,EN_write_3,EN_write_4,EN_write_5,
    write_0,write_1,write_2,write_3,write_4,write_5,
    read_0,read_1,read_2,read_3,read_4,read_5
  }));

  // Combinational chain correctness for each stage
  assert property (read_1 == (EN_write_0 ? write_0 : read_0));
  assert property (read_2 == (EN_write_1 ? write_1 : read_1));
  assert property (read_3 == (EN_write_2 ? write_2 : read_2));
  assert property (read_4 == (EN_write_3 ? write_3 : read_3));
  assert property (read_5 == (EN_write_4 ? write_4 : read_4));

  // Sequential update: new state (read_0) equals last cycle's top-of-chain result
  assert property (read_0 == $past(EN_write_5 ? write_5 : read_5));

  // Hold when no enables
  assert property (!(EN_write_0||EN_write_1||EN_write_2||EN_write_3||EN_write_4||EN_write_5)
                   |=> read_0 == $past(read_0));

  // Priority update winners (concise, explicit cases)
  assert property ( EN_write_5                                      |=> read_0 == $past(write_5));
  assert property (!EN_write_5 &&  EN_write_4                       |=> read_0 == $past(write_4));
  assert property (!EN_write_5 && !EN_write_4 &&  EN_write_3        |=> read_0 == $past(write_3));
  assert property (!EN_write_5 && !EN_write_4 && !EN_write_3 && EN_write_2 |=> read_0 == $past(write_2));
  assert property (!EN_write_5 && !EN_write_4 && !EN_write_3 && !EN_write_2 && EN_write_1
                   |=> read_0 == $past(write_1));
  assert property (!EN_write_5 && !EN_write_4 && !EN_write_3 && !EN_write_2 && !EN_write_1 && EN_write_0
                   |=> read_0 == $past(write_0));

  // Coverage: exercise each priority winner, none, and all asserted
  cover property ( EN_write_5 );
  cover property (!EN_write_5 &&  EN_write_4);
  cover property (!EN_write_5 && !EN_write_4 &&  EN_write_3);
  cover property (!EN_write_5 && !EN_write_4 && !EN_write_3 &&  EN_write_2);
  cover property (!EN_write_5 && !EN_write_4 && !EN_write_3 && !EN_write_2 &&  EN_write_1);
  cover property (!EN_write_5 && !EN_write_4 && !EN_write_3 && !EN_write_2 && !EN_write_1 && EN_write_0);
  cover property (!(EN_write_0||EN_write_1||EN_write_2||EN_write_3||EN_write_4||EN_write_5));
  cover property ( EN_write_5 && EN_write_4 && EN_write_3 && EN_write_2 && EN_write_1 && EN_write_0 );

endmodule