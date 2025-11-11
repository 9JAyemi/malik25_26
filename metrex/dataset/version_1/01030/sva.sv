// SVA for bytewrite_ram_32bits
// Bindable, concise, with shadow model and targeted checks/coverage.

module bytewrite_ram_32bits_sva #(
  parameter SIZE       = 1024,
  parameter ADDR_WIDTH = 12
)(
  input                  clk,
  input      [3:0]       we,
  input      [ADDR_WIDTH-1:0] addr,
  input      [31:0]      din,
  input      [31:0]      dout
);

  // Shadow reference model (matches DUT semantics: read-before-write, byte enables)
  logic [31:0] ref_mem [0:SIZE-1];
  logic [31:0] exp_dout;

  initial begin
    int i;
    for (i=0; i<SIZE; i++) ref_mem[i] = '0;
    exp_dout = '0;
  end

  function automatic [31:0] we2mask(input [3:0] w);
    we2mask = { {8{w[3]}}, {8{w[2]}}, {8{w[1]}}, {8{w[0]}} };
  endfunction

  // Model update (guard against OOR address to keep model safe)
  always_ff @(posedge clk) begin
    if (addr < SIZE) begin
      exp_dout <= ref_mem[addr]; // read-old
      if (we[0]) ref_mem[addr][7:0]    <= din[7:0];
      if (we[1]) ref_mem[addr][15:8]   <= din[15:8];
      if (we[2]) ref_mem[addr][23:16]  <= din[23:16];
      if (we[3]) ref_mem[addr][31:24]  <= din[31:24];
    end
    else begin
      exp_dout <= 'x;
    end
  end

  // Basic interface checks
  a_inputs_known: assert property (@(posedge clk) !$isunknown({we,addr,din}))
    else $error("Inputs contain X/Z");

  a_addr_in_range: assert property (@(posedge clk) addr < SIZE)
    else $error("Address out of range: %0d >= SIZE %0d", addr, SIZE);

  a_dout_known: assert property (@(posedge clk) !$isunknown(dout))
    else $error("dout contains X/Z");

  // Functional checks
  // 1-cycle read latency, read-before-write semantics
  a_read_latency: assert property (@(posedge clk)
      !$isunknown(exp_dout) |-> (dout == exp_dout))
    else $error("Read latency / read-before-write mismatch");

  // Byte-write effect when reading same address next cycle
  // If address held and a write occurred, next-cycle dout equals old&~mask | new&mask.
  a_write_effect: assert property (@(posedge clk)
      ($past(addr) == addr) && $past(we != 4'b0) |->
      dout == ( ($past(exp_dout) & ~we2mask($past(we))) |
                ($past(din)     &  we2mask($past(we))) )
    )
    else $error("Byte-write effect mismatch on held address");

  // Optional: no-write holds old data on held address
  a_no_write_hold: assert property (@(posedge clk)
      ($past(addr) == addr) && $past(we == 4'b0) |->
      dout == $past(exp_dout)
    )
    else $error("Unexpected change with no write on held address");

  // Coverage
  c_we0:  cover property (@(posedge clk) we == 4'b0000);
  c_we1:  cover property (@(posedge clk) $countones(we) == 1);
  c_we2:  cover property (@(posedge clk) $countones(we) == 2);
  c_we3:  cover property (@(posedge clk) $countones(we) == 3);
  c_we4:  cover property (@(posedge clk) we == 4'b1111);
  // Write followed by read of same address (to observe updated value)
  c_write_then_read_same_addr: cover property (@(posedge clk)
      ($past(addr) == addr) && $past(we != 0));
  // Back-to-back writes to same address
  c_b2b_same_addr_writes: cover property (@(posedge clk)
      ($past(addr) == addr) && $past(we != 0) && (we != 0));

endmodule

// Bind to DUT
bind bytewrite_ram_32bits
  bytewrite_ram_32bits_sva #(.SIZE(SIZE), .ADDR_WIDTH(ADDR_WIDTH))
  bytewrite_ram_32bits_sva_i (
    .clk (clk),
    .we  (we),
    .addr(addr),
    .din (din),
    .dout(dout)
  );