// SVA for ERROR_OUTPUT_LOGIC
module ERROR_OUTPUT_LOGIC_sva #(
  parameter int DATA_WIDTH = 1,
  parameter int ADDR_WIDTH = 6
)(
  input  logic                 rst,
  input  logic                 clk,

  // DUT ports
  input  logic                 loop_complete,
  input  logic                 error_detected,
  input  logic [7:0]           error_state,
  input  logic [ADDR_WIDTH-1:0] error_address,
  input  logic [DATA_WIDTH-1:0] expected_data,
  input  logic [DATA_WIDTH-1:0] actual_data,

  input  logic                 tx_data_accepted,
  input  logic                 tx_data_ready,
  input  logic [7:0]           tx_data,

  // DUT internals (bind these hierarchically)
  input  logic                 reg_error_detected,
  input  logic [7:0]           reg_error_state,
  input  logic [ADDR_WIDTH-1:0] reg_error_address,
  input  logic [DATA_WIDTH-1:0] reg_expected_data,
  input  logic [DATA_WIDTH-1:0] reg_actual_data,
  input  logic [7:0]           error_count,
  input  logic [7:0]           output_shift,
  input  logic                 loop_ready,
  input  logic [7:0]           latched_error_count,
  input  logic [10:0]          state,
  input  logic [15:0]          loop_count,
  input  logic [15:0]          latched_loop_count
);

  // State bit indices (one-hot)
  localparam int START_B               = 0;
  localparam int ERROR_COUNT_HEADER_B  = 1;
  localparam int ERROR_COUNT_COUNT_B   = 2;
  localparam int CR_B                  = 3;
  localparam int LF_B                  = 4;
  localparam int ERROR_HEADER_B        = 5;
  localparam int ERROR_STATE_B         = 6;
  localparam int ERROR_ADDRESS_B       = 7;
  localparam int ERROR_EXPECTED_DATA_B = 8;
  localparam int ERROR_ACTUAL_DATA_B   = 9;
  localparam int LOOP_COUNT_B          = 10;

  // Convenient state bits
  wire sSTART               = state[START_B];
  wire sERROR_COUNT_HEADER  = state[ERROR_COUNT_HEADER_B];
  wire sERROR_COUNT_COUNT   = state[ERROR_COUNT_COUNT_B];
  wire sCR                  = state[CR_B];
  wire sLF                  = state[LF_B];
  wire sERROR_HEADER        = state[ERROR_HEADER_B];
  wire sERROR_STATE         = state[ERROR_STATE_B];
  wire sERROR_ADDRESS       = state[ERROR_ADDRESS_B];
  wire sERROR_EXPECTED_DATA = state[ERROR_EXPECTED_DATA_B];
  wire sERROR_ACTUAL_DATA   = state[ERROR_ACTUAL_DATA_B];
  wire sLOOP_COUNT          = state[LOOP_COUNT_B];

  // Helpers
  function automatic bit last_chunk(input int w, input int sh);
    return (sh+8) >= w;
  endfunction

  // Reset behavior
  assert property (@(posedge clk) rst |-> (sSTART && !tx_data_ready && (tx_data==8'h00) && (error_count==8'h00) && !reg_error_detected && (loop_count==16'h0000) && !loop_ready))
    else $error("Reset values mismatch");

  // One-hot state
  assert property (@(posedge clk) disable iff (rst) $onehot(state))
    else $error("State not one-hot");

  // START arbitration
  assert property (@(posedge clk) disable iff (rst) $past(sSTART && reg_error_detected) |-> sERROR_HEADER)
    else $error("START -> ERROR_HEADER priority broken");
  assert property (@(posedge clk) disable iff (rst) $past(sSTART && !reg_error_detected && loop_ready) |-> sERROR_COUNT_HEADER)
    else $error("START -> ERROR_COUNT_HEADER transition broken");

  // Handshake: ready holds until accepted, data stable while held, deassert next after accept
  assert property (@(posedge clk) disable iff (rst) (tx_data_ready && !tx_data_accepted) |=> tx_data_ready)
    else $error("tx_data_ready dropped without accept");
  assert property (@(posedge clk) disable iff (rst) (tx_data_ready && !tx_data_accepted) |=> $stable(tx_data))
    else $error("tx_data changed while held ready");
  assert property (@(posedge clk) disable iff (rst) (tx_data_ready && tx_data_accepted) |=> !tx_data_ready)
    else $error("tx_data_ready not deasserted after accept");

  // Any ready pulse must come from a transmitting state
  assert property (@(posedge clk) disable iff (rst)
                    $rose(tx_data_ready) |->
                    $past(sERROR_COUNT_HEADER | sERROR_COUNT_COUNT | sLOOP_COUNT | sCR | sLF |
                          sERROR_HEADER | sERROR_STATE | sERROR_ADDRESS | sERROR_EXPECTED_DATA | sERROR_ACTUAL_DATA))
    else $error("tx_data_ready rose outside of valid states");

  // Byte content and next-state checks at each transmit point (use $past state on ready rise)
  assert property (@(posedge clk) disable iff (rst)
                    $rose(tx_data_ready) && $past(sERROR_COUNT_HEADER)
                    |-> (tx_data==8'h4C) && sERROR_COUNT_COUNT)
    else $error("ERROR_COUNT_HEADER byte/next-state incorrect");

  assert property (@(posedge clk) disable iff (rst)
                    $rose(tx_data_ready) && $past(sERROR_COUNT_COUNT)
                    |-> (tx_data==$past(latched_error_count)) && sLOOP_COUNT)
    else $error("ERROR_COUNT_COUNT byte/next-state incorrect");

  // LOOP_COUNT two bytes: LSB then MSB, then CR and loop_ready cleared
  assert property (@(posedge clk) disable iff (rst)
                    $rose(tx_data_ready) && $past(sLOOP_COUNT) && ($past(output_shift)==8'd0)
                    |-> (tx_data==$past(latched_loop_count[7:0])) && sLOOP_COUNT)
    else $error("LOOP_COUNT LSB incorrect");
  assert property (@(posedge clk) disable iff (rst)
                    $rose(tx_data_ready) && $past(sLOOP_COUNT) && ($past(output_shift)==8'd8)
                    |-> (tx_data==$past(latched_loop_count[15:8])) && sCR && !loop_ready)
    else $error("LOOP_COUNT MSB/next-state/loop_ready incorrect");

  assert property (@(posedge clk) disable iff (rst)
                    $rose(tx_data_ready) && $past(sCR)
                    |-> (tx_data==8'h0D) && sLF)
    else $error("CR byte/next-state incorrect");

  assert property (@(posedge clk) disable iff (rst)
                    $rose(tx_data_ready) && $past(sLF)
                    |-> (tx_data==8'h0A) && sSTART)
    else $error("LF byte/next-state incorrect");

  // Error report path
  assert property (@(posedge clk) disable iff (rst)
                    $rose(tx_data_ready) && $past(sERROR_HEADER)
                    |-> (tx_data==8'h45) && sERROR_STATE)
    else $error("ERROR_HEADER byte/next-state incorrect");

  assert property (@(posedge clk) disable iff (rst)
                    $rose(tx_data_ready) && $past(sERROR_STATE)
                    |-> (tx_data==$past(reg_error_state)) && sERROR_ADDRESS)
    else $error("ERROR_STATE byte/next-state incorrect");

  // ERROR_ADDRESS chunks
  assert property (@(posedge clk) disable iff (rst)
                    $rose(tx_data_ready) && $past(sERROR_ADDRESS) &&
                    !last_chunk(ADDR_WIDTH, $past(output_shift))
                    |-> (tx_data==($past(reg_error_address) >> $past(output_shift))) && sERROR_ADDRESS)
    else $error("ERROR_ADDRESS non-final chunk incorrect");
  assert property (@(posedge clk) disable iff (rst)
                    $rose(tx_data_ready) && $past(sERROR_ADDRESS) &&
                    last_chunk(ADDR_WIDTH, $past(output_shift))
                    |-> (tx_data==($past(reg_error_address) >> $past(output_shift))) && sERROR_EXPECTED_DATA)
    else $error("ERROR_ADDRESS final chunk/next-state incorrect");

  // ERROR_EXPECTED_DATA chunks
  assert property (@(posedge clk) disable iff (rst)
                    $rose(tx_data_ready) && $past(sERROR_EXPECTED_DATA) &&
                    !last_chunk(DATA_WIDTH, $past(output_shift))
                    |-> (tx_data==($past(reg_expected_data) >> $past(output_shift))) && sERROR_EXPECTED_DATA)
    else $error("EXPECTED_DATA non-final chunk incorrect");
  assert property (@(posedge clk) disable iff (rst)
                    $rose(tx_data_ready) && $past(sERROR_EXPECTED_DATA) &&
                    last_chunk(DATA_WIDTH, $past(output_shift))
                    |-> (tx_data==($past(reg_expected_data) >> $past(output_shift))) && sERROR_ACTUAL_DATA)
    else $error("EXPECTED_DATA final chunk/next-state incorrect");

  // ERROR_ACTUAL_DATA chunks and clear reg_error_detected at end
  assert property (@(posedge clk) disable iff (rst)
                    $rose(tx_data_ready) && $past(sERROR_ACTUAL_DATA) &&
                    !last_chunk(DATA_WIDTH, $past(output_shift))
                    |-> (tx_data==($past(reg_actual_data) >> $past(output_shift))) && sERROR_ACTUAL_DATA)
    else $error("ACTUAL_DATA non-final chunk incorrect");
  assert property (@(posedge clk) disable iff (rst)
                    $rose(tx_data_ready) && $past(sERROR_ACTUAL_DATA) &&
                    last_chunk(DATA_WIDTH, $past(output_shift))
                    |-> (tx_data==($past(reg_actual_data) >> $past(output_shift))) && sCR && !reg_error_detected)
    else $error("ACTUAL_DATA final chunk/next-state/clear reg_error_detected incorrect");

  // Error capture: latch-on-first, then hold while latched
  assert property (@(posedge clk) disable iff (rst)
                    (error_detected && !reg_error_detected)
                    |=> (reg_error_detected &&
                         reg_error_state   == $past(error_state)   &&
                         reg_error_address == $past(error_address) &&
                         reg_expected_data == $past(expected_data) &&
                         reg_actual_data   == $past(actual_data)))
    else $error("Error capture failed");
  assert property (@(posedge clk) disable iff (rst)
                    reg_error_detected |=> $stable({reg_error_state,reg_error_address,reg_expected_data,reg_actual_data}))
    else $error("Captured error fields changed while latched");

  // Error count: increment with detect until saturation, then hold
  assert property (@(posedge clk) disable iff (rst)
                    (error_detected && ($past(error_count) < 8'hFF)) |=> (error_count == $past(error_count)+1))
    else $error("error_count did not increment");
  assert property (@(posedge clk) disable iff (rst)
                    (error_detected && ($past(error_count) == 8'hFF)) |=> (error_count == 8'hFF))
    else $error("error_count did not saturate");

  // Loop accounting: loop_count increments; first loop_ready latches counts and clears error_count
  assert property (@(posedge clk) disable iff (rst)
                    loop_complete |=> (loop_count == $past(loop_count)+1))
    else $error("loop_count did not increment on loop_complete");

  assert property (@(posedge clk) disable iff (rst)
                    (loop_complete && !$past(loop_ready))
                    |=> (loop_ready &&
                         latched_error_count == $past(error_count) &&
                         latched_loop_count  == $past(loop_count)  &&
                         error_count == 8'h00))
    else $error("Loop latch/clear behavior incorrect");

  // Coverage
  cover property (@(posedge clk) disable iff (rst) $rose(tx_data_ready) && $past(sERROR_COUNT_HEADER)); // emitted 'L'
  cover property (@(posedge clk) disable iff (rst) $rose(tx_data_ready) && $past(sERROR_HEADER));       // emitted 'E'
  if (ADDR_WIDTH > 8)
    cover property (@(posedge clk) disable iff (rst) $rose(tx_data_ready) && $past(sERROR_ADDRESS) && ($past(output_shift)==8)); // multi-byte addr
  if (DATA_WIDTH > 8)
    cover property (@(posedge clk) disable iff (rst) $rose(tx_data_ready) && $past(sERROR_EXPECTED_DATA) && ($past(output_shift)==8)); // multi-byte data
  cover property (@(posedge clk) disable iff (rst) (error_count==8'hFF) && error_detected); // saturation hit
  cover property (@(posedge clk) disable iff (rst) $rose(loop_ready)); // loop report latched

endmodule

// Example bind (connect internals by hierarchy):
// bind ERROR_OUTPUT_LOGIC ERROR_OUTPUT_LOGIC_sva #(.DATA_WIDTH(DATA_WIDTH), .ADDR_WIDTH(ADDR_WIDTH)) i_sva (.*,
//   .reg_error_detected(reg_error_detected),
//   .reg_error_state(reg_error_state),
//   .reg_error_address(reg_error_address),
//   .reg_expected_data(reg_expected_data),
//   .reg_actual_data(reg_actual_data),
//   .error_count(error_count),
//   .output_shift(output_shift),
//   .loop_ready(loop_ready),
//   .latched_error_count(latched_error_count),
//   .state(state),
//   .loop_count(loop_count),
//   .latched_loop_count(latched_loop_count));