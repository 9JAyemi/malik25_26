// SVA checker for lifo_top
// Bind once per DUT instance
bind lifo_top lifo_top_sva #(
  .DATA_WIDTH(DATA_WIDTH),
  .NUM_ENTRIES(NUM_ENTRIES),
  .OPCODE_WIDTH(OPCODE_WIDTH)
) lifo_top_sva_i();

module lifo_top_sva #(parameter int DATA_WIDTH=4,
                      parameter int NUM_ENTRIES=4,
                      parameter int OPCODE_WIDTH=2) ();

  localparam int LINE_WIDTH = DATA_WIDTH + OPCODE_WIDTH;

  // Encodings (mirror DUT macros)
  localparam [1:0] POP        = 2'b01;
  localparam [1:0] PUSH       = 2'b10;
  localparam [1:0] DO_NOTHING = 2'b00;
  localparam [1:0] INVALID    = 2'b11;

  // Access DUT signals by name in bound scope
  // wire clk, reset, vector_in, data_out, empty_flag, full_flag, lifo_valid_invalid_bit, lifo_head_pos, lifo_tail_pos;

  // Decode inputs (as DUT does)
  wire [OPCODE_WIDTH-1:0] opcode = vector_in[LINE_WIDTH-1 -: OPCODE_WIDTH];
  wire [DATA_WIDTH-1:0]   din    = vector_in[LINE_WIDTH-OPCODE_WIDTH-1 -: DATA_WIDTH];

  // Simple reference stack model for functional checking
  logic [DATA_WIDTH-1:0] stack[$];
  int unsigned model_size_q;
  logic [DATA_WIDTH-1:0] model_top_q;

  always_ff @(posedge clk) begin
    if (reset) begin
      stack.delete();
      model_size_q <= 0;
      model_top_q  <= '0;
    end else begin
      if (opcode == PUSH && model_size_q < NUM_ENTRIES) stack.push_back(din);
      else if (opcode == POP && model_size_q > 0)       stack.pop_back();

      model_size_q <= stack.size(); // holds pre-op size for next cycle’s checks
      model_top_q  <= (stack.size()>0) ? stack[stack.size()-1] : '0;
    end
  end

  default clocking cb @(posedge clk); endclocking

  // Invariants and flag correctness
  assert property (disable iff (reset) !(empty_flag && full_flag));
  assert property (disable iff (reset) empty_flag == (model_size_q == 0));
  assert property (disable iff (reset) full_flag  == (model_size_q == NUM_ENTRIES));

  // Valid bitmap matches model occupancy; pointers in range
  assert property (disable iff (reset) $countones(lifo_valid_invalid_bit) == model_size_q);
  assert property (disable iff (reset) lifo_head_pos < NUM_ENTRIES);
  assert property (disable iff (reset) lifo_tail_pos < NUM_ENTRIES);

  // Occupancy changes with operations
  assert property (disable iff (reset)
                   (opcode==PUSH && model_size_q < NUM_ENTRIES) |=> model_size_q == $past(model_size_q)+1);
  assert property (disable iff (reset)
                   (opcode==POP  && model_size_q > 0)          |=> model_size_q == $past(model_size_q)-1);

  // Data behavior
  assert property (disable iff (reset)
                   (opcode==POP && model_size_q>0) |-> (! $isunknown(data_out) && data_out == model_top_q));
  assert property (disable iff (reset)
                   (opcode==POP && model_size_q==0) |-> $isunknown(data_out));
  assert property (disable iff (reset)
                   (opcode inside {DO_NOTHING, INVALID}) |-> $isunknown(data_out));

  // Minimal coverage
  cover property (disable iff (reset) full_flag);
  cover property (disable iff (reset) empty_flag);
  cover property (disable iff (reset)
                  (opcode==PUSH && model_size_q<NUM_ENTRIES)[*2] ##1
                  (opcode==POP  && model_size_q>0)[*2]);
  cover property (disable iff (reset) (opcode inside {DO_NOTHING, INVALID}));

endmodule