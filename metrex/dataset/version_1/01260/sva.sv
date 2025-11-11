// SVA for ROM_TEST
// Binds into the DUT and checks FSM, addressing, error reporting, and loop behavior concisely.

module ROM_TEST_sva #(
  parameter int ADDR_WIDTH   = 6,
  parameter int DATA_WIDTH   = 1,
  parameter int ADDRESS_STEP = 1,
  parameter int MAX_ADDRESS  = 63
) (
  input  logic                       rst,
  input  logic                       clk,
  input  logic [DATA_WIDTH-1:0]      read_data,
  input  logic [ADDR_WIDTH-1:0]      read_address,
  input  logic [DATA_WIDTH-1:0]      rom_read_data,
  input  logic [ADDR_WIDTH-1:0]      rom_read_address,
  input  logic                       loop_complete,
  input  logic                       error,
  input  logic [7:0]                 error_state,
  input  logic [ADDR_WIDTH-1:0]      error_address,
  input  logic [DATA_WIDTH-1:0]      expected_data,
  input  logic [DATA_WIDTH-1:0]      actual_data,
  // internal DUT signals
  input  logic [7:0]                 state,
  input  logic [1:0]                 delay
);

  localparam byte START       = 8'd1;
  localparam byte VERIFY_INIT = 8'd2;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Parameter sanity
  initial begin
    assert (ADDRESS_STEP >= 1)
      else $error("ADDRESS_STEP must be >= 1");
    assert (MAX_ADDRESS < (1<<ADDR_WIDTH))
      else $error("MAX_ADDRESS must fit within ADDR_WIDTH");
  end

  // Reset behavior (synchronous)
  assert property (@(posedge clk) rst |-> (state==START && error==1'b0));

  // START state outputs and next-state
  assert property (state==START |-> (loop_complete==0 && read_address==0 && rom_read_address==0 && error==0));
  assert property (state==START |=> state==VERIFY_INIT);
  // delay does not change in START
  assert property (state==START |-> $stable(delay));

  // delay increments modulo-4 while in VERIFY_INIT
  assert property (state==VERIFY_INIT |=> delay == ($past(delay)+2'd1));

  // Addresses always equal
  assert property (read_address == rom_read_address);

  // Addresses only change at VERIFY_INIT with delay==1
  assert property ((state==VERIFY_INIT && delay!=2'd1) |-> ($stable(read_address) && $stable(rom_read_address)));

  // Increment path (no wrap) at delay==1
  assert property (
    (state==VERIFY_INIT && delay==2'd1 &&
     ($unsigned($past(read_address)) + ADDRESS_STEP) <= MAX_ADDRESS)
    |-> (read_address == $past(read_address)+ADDRESS_STEP &&
         rom_read_address == $past(rom_read_address)+ADDRESS_STEP &&
         loop_complete==0 && state==VERIFY_INIT)
  );

  // Wrap path at delay==1
  assert property (
    (state==VERIFY_INIT && delay==2'd1 &&
     ($unsigned($past(read_address)) + ADDRESS_STEP) > MAX_ADDRESS)
    |-> (read_address==0 && rom_read_address==0 && loop_complete==1)
  );
  // After wrap we go to START next cycle and pulse loop_complete for 1 cycle
  assert property (
    (state==VERIFY_INIT && delay==2'd1 &&
     ($unsigned($past(read_address)) + ADDRESS_STEP) > MAX_ADDRESS)
    |=> (state==START)
  );
  assert property (loop_complete |-> (state==VERIFY_INIT && delay==2'd1) ##1 !loop_complete);

  // Address range is always within [0..MAX_ADDRESS]
  assert property ($unsigned(read_address) <= MAX_ADDRESS);
  assert property ($unsigned(rom_read_address) <= MAX_ADDRESS);

  // Compare phase at delay==0: error reflects data mismatch
  assert property ((state==VERIFY_INIT && delay==2'd0) |-> (error == (rom_read_data != read_data)));

  // When mismatch, capture diagnostics
  assert property (
    (state==VERIFY_INIT && delay==2'd0 && (rom_read_data != read_data))
    |-> (error &&
         error_state == VERIFY_INIT &&
         error_address == read_address &&
         expected_data == rom_read_data &&
         actual_data   == read_data)
  );

  // error only changes on compare cycles (delay==0 in VERIFY_INIT)
  assert property ((error != $past(error)) |-> $past(state==VERIFY_INIT && delay==2'd0));

  // Coverage
  //  - See all delay slots while in VERIFY_INIT
  cover property (state==VERIFY_INIT && delay==2'd0 ##1 state==VERIFY_INIT && delay==2'd1 ##1 state==VERIFY_INIT && delay==2'd2 ##1 state==VERIFY_INIT && delay==2'd3);
  //  - Complete a full loop (wrap event)
  cover property (state==VERIFY_INIT && delay==2'd1 && ($unsigned($past(read_address))+ADDRESS_STEP)>MAX_ADDRESS ##0 loop_complete ##1 state==START);
  //  - Observe a mismatch capture
  cover property (state==VERIFY_INIT && delay==2'd0 && (rom_read_data != read_data) && error);

endmodule

// Bind into the DUT
bind ROM_TEST ROM_TEST_sva #(
  .ADDR_WIDTH(ADDR_WIDTH),
  .DATA_WIDTH(DATA_WIDTH),
  .ADDRESS_STEP(ADDRESS_STEP),
  .MAX_ADDRESS(MAX_ADDRESS)
) u_rom_test_sva (
  .rst(rst),
  .clk(clk),
  .read_data(read_data),
  .read_address(read_address),
  .rom_read_data(rom_read_data),
  .rom_read_address(rom_read_address),
  .loop_complete(loop_complete),
  .error(error),
  .error_state(error_state),
  .error_address(error_address),
  .expected_data(expected_data),
  .actual_data(actual_data),
  .state(state),
  .delay(delay)
);