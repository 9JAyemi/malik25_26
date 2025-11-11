// SVA checker for regfile
// Binds to the DUT and verifies protocol, data integrity, and provides concise coverage.

module regfile_sva #(parameter int DEPTH = 8, parameter int WIDTH = 8)
(
  input  logic                  clk,
  input  logic                  wren,
  input  logic [WIDTH-1:0]      data_in,
  input  logic [DEPTH-1:0]      wraddr,
  input  logic [DEPTH-1:0]      rdaddr,
  input  logic [WIDTH-1:0]      data_out
);

  default clocking cb @(posedge clk); endclocking

  // Simple shadow model to check DUT behavior on reads
  logic [WIDTH-1:0] shadow_mem [DEPTH-1:0];
  bit               wrote      [DEPTH-1:0];

  // Initialize tracking
  initial begin
    for (int i = 0; i < DEPTH; i++) begin
      wrote[i] = 1'b0;
      shadow_mem[i] = 'x;
    end
  end

  // Update shadow model on valid writes
  always_ff @(posedge clk) begin
    if (wren && !$isunknown({wraddr, data_in}) && ($unsigned(wraddr) < DEPTH)) begin
      shadow_mem[$unsigned(wraddr)] <= data_in;
      wrote[$unsigned(wraddr)]      <= 1'b1;
    end
  end

  // Basic sanity: control and address use
  assert property (!$isunknown(wren)))
    else $error("wren is X/Z at clk edge");

  assert property (wren |-> ($unsigned(wraddr) < DEPTH))
    else $error("Write address out of range");

  assert property (!wren |-> ($unsigned(rdaddr) < DEPTH))
    else $error("Read address out of range");

  assert property (wren |-> !$isunknown({wraddr, data_in}))
    else $error("Write has X/Z address or data");

  assert property (!wren |-> !$isunknown(rdaddr))
    else $error("Read has X/Z address");

  // Data_out protocol
  assert property (wren |=> data_out == $past(data_out))
    else $error("data_out changed during write cycle");

  assert property ($changed(data_out) |-> !wren)
    else $error("data_out changed outside a read cycle");

  // Functional read check against shadow model
  assert property ((!wren) && ($unsigned(rdaddr) < DEPTH) && wrote[$unsigned(rdaddr)]
                   |-> data_out == shadow_mem[$unsigned(rdaddr)])
    else $error("Read data mismatch vs shadow model");

  // Optional: read must reflect the value present in reg file on the previous cycle
  // Uncomment if tools allow internal array reference in bound scope.
  // assert property ((!wren) && ($unsigned(rdaddr) < DEPTH)
  //                  |-> data_out == $past(shadow_mem[$unsigned(rdaddr)]))
  //   else $error("Read timing mismatch");

  // Coverage
  cover property (wren && ($unsigned(wraddr) < DEPTH));   // any valid write
  cover property (!wren && ($unsigned(rdaddr) < DEPTH));  // any valid read

  // Per-address: write then later read back same location
  generate
    for (genvar i = 0; i < DEPTH; i++) begin : COV_ADDR
      cover property ( (wren && ($unsigned(wraddr) == i))
                       ##[1:$] (!wren && ($unsigned(rdaddr) == i) && wrote[i]
                                && data_out == shadow_mem[i]) );
    end
  endgenerate

endmodule

// Bind the checker to all regfile instances
bind regfile regfile_sva #(.DEPTH(DEPTH), .WIDTH(WIDTH)) regfile_sva_i
(
  .clk(clk),
  .wren(wren),
  .data_in(data_in),
  .wraddr(wraddr),
  .rdaddr(rdaddr),
  .data_out(data_out)
);