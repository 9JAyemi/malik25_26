// SVA checker for mem_test
module mem_test_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic [7:0]  addr,
  input  logic [7:0]  din,
  input  logic        mem_en,
  input  logic [7:0]  dout,
  input  logic        error,

  // bind-internal DUT signals
  input  logic [7:0]  read_data,
  input  logic        write_en,
  input  logic        read_en,
  input  logic [7:0]  error_addr,
  input  logic [7:0]  mem_addr,
  input  logic        error_wire,
  input  logic        error_reg
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Simple structural checks
  assert property (dout == read_data);
  assert property (mem_addr == addr);
  assert property ($past(!rst) |-> write_en == $past(mem_en));
  assert property ($past(!rst) |-> read_en  == $past(mem_en));

  // Read-data behavior
  assert property ($past(!rst && !mem_en) |-> read_data == $past(read_data));

  // Error-wire combinational definition
  assert property (error_wire == (write_en && read_en && (din != read_data)));

  // Error register/update semantics
  assert property (error == error_reg);
  assert property (error == ($past(mem_en) && $past(error_wire)));
  assert property (error |-> (error_addr == $past(addr)));
  assert property ($past(mem_en) && !$past(error_wire) |-> (!error && $stable(error_addr)));

  // Lightweight scoreboard to check read-after-write semantics
  bit [7:0] exp_mem [0:255];
  bit       valid   [0:255];

  // Model update (same-cycle as DUT write). Preponed sampling sees pre-update value.
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      for (int i = 0; i < 256; i++) begin
        exp_mem[i] <= '0;
        valid[i]   <= 1'b0;
      end
    end else begin
      if (mem_en) begin
        exp_mem[addr] <= din;
        valid[addr]   <= 1'b1;
      end
    end
  end

  // When a read occurs (previous cycle mem_en), read_data must equal the pre-write value
  assert property ($past(!rst && mem_en && valid[addr]) |-> read_data == $past(exp_mem[addr]));

  // Coverage
  cover property (rst ##1 !rst);
  cover property ($past(mem_en));                  // exercised read/write
  cover property ($past(mem_en) && !error);        // non-error cycle
  cover property ($past(mem_en) && error);         // error cycle
  cover property (mem_en ##1 mem_en);              // back-to-back access
  cover property (mem_en ##1 (mem_en && addr != $past(addr))); // address change
endmodule

// Bind to DUT
bind mem_test mem_test_sva sva (
  .clk        (clk),
  .rst        (rst),
  .addr       (addr),
  .din        (din),
  .mem_en     (mem_en),
  .dout       (dout),
  .error      (error),
  .read_data  (read_data),
  .write_en   (write_en),
  .read_en    (read_en),
  .error_addr (error_addr),
  .mem_addr   (mem_addr),
  .error_wire (error_wire),
  .error_reg  (error_reg)
);