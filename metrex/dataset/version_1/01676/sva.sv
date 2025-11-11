// SVA for ROM_reader — concise, quality-focused
// Bind into DUT to access internal rom[]
module ROM_reader_sva #(parameter ROM_SIZE=16)
(
  input logic        clk,
  input logic        read,
  input logic [3:0]  address,
  input logic [7:0]  data_out
);
  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Inputs sanity when used
  a_no_x_on_read: assert property (read |-> !$isunknown(address));

  // Valid read updates output to ROM[address] (sampled at read cycle)
  a_read_updates: assert property (
    past_valid && $past(read) && $past(address) < ROM_SIZE
      |-> data_out == $past(rom[$past(address)])
  );

  // Otherwise output holds its previous value
  a_hold_when_idle_or_oob: assert property (
    past_valid && (!$past(read) || $past(address) >= ROM_SIZE)
      |-> data_out == $past(data_out)
  );

  // Any change on data_out must be due to a valid read
  a_change_implies_read: assert property (
    past_valid && data_out != $past(data_out)
      |-> $past(read) && $past(address) < ROM_SIZE
  );

  // ROM contents remain constant after initialization
  genvar i;
  generate
    for (i = 0; i < ROM_SIZE; i++) begin : G_ROM_CONST
      a_rom_const: assert property (past_valid |-> $stable(rom[i]));
      // Coverage: hit each address with a read
      c_addr_read:  cover property (read && address == i);
    end
  endgenerate

  // Coverage: observe at least one valid update and one hold
  c_update: cover property (
    past_valid && $past(read) && $past(address) < ROM_SIZE ##1
      data_out == $past(rom[$past(address)])
  );
  c_hold: cover property (
    past_valid && !$past(read) ##1 data_out == $past(data_out)
  );
endmodule

bind ROM_reader ROM_reader_sva #(.ROM_SIZE(ROM_SIZE)) ROM_reader_sva_i (.*);