// SVA for altera_up_av_config_auto_init
// Concise, high-quality checks and coverage. Bind this module to the DUT.

module altera_up_av_config_auto_init_sva
  #(parameter AW = 5, DW = 23, ROM_SIZE = 50)
(
  input  logic                 clk,
  input  logic                 reset,
  input  logic                 clear_error,
  input  logic                 ack,
  input  logic                 transfer_complete,
  input  logic [DW:0]          rom_data,
  input  logic [DW:0]          data_out,
  input  logic                 transfer_data,
  input  logic [AW:0]          rom_address,
  input  logic                 auto_init_complete,
  input  logic                 auto_init_error,
  input  logic                 toggle_next_transfer
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Combinational definition check
  assert property (toggle_next_transfer == (transfer_data && transfer_complete))
    else $error("toggle_next_transfer must equal transfer_data & transfer_complete");

  // data_out register behavior
  assert property (past_valid |-> data_out == ($past(reset) ? '0 : $past(rom_data)))
    else $error("data_out update mismatch");

  // transfer_data register behavior
  assert property (past_valid |-> transfer_data == ($past(reset) ? 1'b0
                                                      : (!$past(auto_init_complete) && !$past(transfer_complete))))
    else $error("transfer_data update mismatch");

  // rom_address register behavior (reset/hold/increment on toggle)
  assert property (past_valid |-> rom_address == ($past(reset) ? '0
                                                      : ($past(toggle_next_transfer) ? $past(rom_address)+'h1
                                                                                      : $past(rom_address))))
    else $error("rom_address update mismatch");

  // auto_init_complete: set when last address toggles; sticky until reset
  assert property (past_valid |-> auto_init_complete ==
                               ($past(reset) ? 1'b0
                                             : ($past(auto_init_complete) ||
                                                ($past(toggle_next_transfer) && ($past(rom_address) == ROM_SIZE-1)))))
    else $error("auto_init_complete update mismatch");

  // auto_init_complete can only rise at last toggle
  assert property ($rose(auto_init_complete) |-> $past(toggle_next_transfer) &&
                                            ($past(rom_address) == ROM_SIZE-1))
    else $error("auto_init_complete rose without last toggle at ROM_SIZE-1");

  // After last toggle at ROM_SIZE-1, rom_address becomes ROM_SIZE
  assert property ($past(toggle_next_transfer && (rom_address == ROM_SIZE-1)) |-> rom_address == ROM_SIZE)
    else $error("rom_address did not advance to ROM_SIZE after last toggle");

  // Once complete, no further address movement and transfer_data stays low
  assert property ($past(auto_init_complete) |-> rom_address == $past(rom_address))
    else $error("rom_address moved after auto_init_complete");
  assert property ($rose(auto_init_complete) |=> !transfer_data)
    else $error("transfer_data not deasserted after auto_init_complete");

  // auto_init_error: priority set on (toggle & ack), else clear on clear_error, else hold; reset clears
  assert property (past_valid |-> auto_init_error ==
                               ($past(reset) ? 1'b0
                                             : ($past(toggle_next_transfer && ack) ? 1'b1
                                               : ($past(clear_error) ? 1'b0
                                                 : $past(auto_init_error)))))
    else $error("auto_init_error update mismatch");

  // Priority: if ack and clear_error happen together with toggle, error must set
  assert property ($past(toggle_next_transfer && ack && clear_error) |-> auto_init_error)
    else $error("auto_init_error priority violated (ack must dominate clear_error)");

  // Transfer halts on either auto_init_complete or transfer_complete
  assert property (past_valid && $past(auto_init_complete) |-> !transfer_data)
    else $error("transfer_data not low after auto_init_complete");
  assert property (past_valid && $past(transfer_complete) |-> !transfer_data)
    else $error("transfer_data not low after transfer_complete");

  // Basic reset effect (next-cycle zeros)
  assert property ($past(reset) |-> (data_out == '0 &&
                                     transfer_data == 1'b0 &&
                                     rom_address == '0 &&
                                     auto_init_complete == 1'b0 &&
                                     auto_init_error == 1'b0))
    else $error("Registers not cleared after reset");

  // Coverage
  cover property (past_valid && $fell(reset) ##1 transfer_data);
  cover property (past_valid && $past(rom_address=='0) ##[1:$] $rose(toggle_next_transfer));
  cover property (past_valid && ($past(rom_address)==ROM_SIZE-1) && $past(toggle_next_transfer) ##1 auto_init_complete);
  cover property (past_valid && $past(toggle_next_transfer && ack) ##1 auto_init_error);
  cover property (past_valid && $past(auto_init_error) && $past(clear_error) ##1 !auto_init_error);

endmodule

// Bind into the DUT
bind altera_up_av_config_auto_init
  altera_up_av_config_auto_init_sva #(.AW(AW), .DW(DW), .ROM_SIZE(ROM_SIZE)) u_sva (
    .clk(clk),
    .reset(reset),
    .clear_error(clear_error),
    .ack(ack),
    .transfer_complete(transfer_complete),
    .rom_data(rom_data),
    .data_out(data_out),
    .transfer_data(transfer_data),
    .rom_address(rom_address),
    .auto_init_complete(auto_init_complete),
    .auto_init_error(auto_init_error),
    .toggle_next_transfer(toggle_next_transfer)
  );