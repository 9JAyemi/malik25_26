// SystemVerilog Assertions for DataMemory
// Concise, high-quality checks + coverage. Bind into the DUT.

module DataMemory_sva #(parameter int WIDTH=8, DEPTH=256)
(
  input  logic                    Clk,
  input  logic                    rdEn,
  input  logic                    wrEn,
  input  logic [WIDTH-1:0]        wrData,
  input  logic [7:0]              addr,
  input  logic [WIDTH-1:0]        Data,
  // access internal memory by reference
  ref    logic [WIDTH-1:0]        memory [DEPTH]
);

  // Basic hygiene
  assert property (@(posedge Clk) !$isunknown({rdEn,wrEn}));
  assert property (@(posedge Clk) rdEn |-> (!$isunknown(addr) && addr < DEPTH));
  assert property (@(posedge Clk) wrEn |-> (!$isunknown(addr) && addr < DEPTH && !$isunknown(wrData)));

  // Read semantics: read returns pre-state memory at current addr (read-before-write)
  property p_read_value;
    int unsigned a;
    @(posedge Clk)
      (rdEn && !$isunknown(addr) && addr < DEPTH, a = addr)
      |-> ##0 (Data === $past(memory[a]));
  endproperty
  assert property (p_read_value);

  // When not reading, output must be unknown (design forces X)
  assert property (@(posedge Clk) (!rdEn) |-> ##0 $isunknown(Data));

  // Write semantics: write updates memory location on next cycle
  property p_write_updates_mem;
    int unsigned a; logic [WIDTH-1:0] d;
    @(posedge Clk)
      (wrEn && !$isunknown(addr) && addr < DEPTH && !$isunknown(wrData), a = addr, d = wrData)
      |-> ##1 (memory[a] === d);
  endproperty
  assert property (p_write_updates_mem);

  // Read after write to same address returns the new data (next cycle)
  property p_raw_next_cycle_newdata;
    int unsigned a; logic [WIDTH-1:0] d;
    @(posedge Clk)
      (wrEn && !$isunknown(addr) && addr < DEPTH && !$isunknown(wrData), a = addr, d = wrData)
      ##1 (rdEn && addr == a) |-> ##0 (Data === d);
  endproperty
  assert property (p_raw_next_cycle_newdata);

  // Coverage

  // basic ops
  cover property (@(posedge Clk) wrEn);
  cover property (@(posedge Clk) rdEn);
  cover property (@(posedge Clk) wrEn && rdEn);

  // edge addresses
  cover property (@(posedge Clk) wrEn && addr == 0);
  cover property (@(posedge Clk) wrEn && addr == (DEPTH-1));
  cover property (@(posedge Clk) rdEn && addr == 0);
  cover property (@(posedge Clk) rdEn && addr == (DEPTH-1));

  // write then read same address next cycle
  property c_wr_then_rd_same_addr;
    int unsigned a;
    @(posedge Clk)
      (wrEn && !$isunknown(addr) && addr < DEPTH, a = addr)
      ##1 (rdEn && addr == a);
  endproperty
  cover property (c_wr_then_rd_same_addr);

  // back-to-back writes to same address
  property c_back2back_writes_same_addr;
    int unsigned a;
    @(posedge Clk)
      (wrEn && !$isunknown(addr) && addr < DEPTH, a = addr)
      ##1 (wrEn && addr == a);
  endproperty
  cover property (c_back2back_writes_same_addr);

  // observe X-to-known transition on a read (if memory at addr is known)
  cover property (@(posedge Clk)
                   !rdEn ##1 (rdEn && !$isunknown(addr) && addr < DEPTH && !($isunknown($past(memory[addr])))));

endmodule

// Bind into the DUT
bind DataMemory DataMemory_sva #(.WIDTH(WIDTH), .DEPTH(DEPTH))
  DataMemory_sva_i ( .Clk(Clk), .rdEn(rdEn), .wrEn(wrEn),
                     .wrData(wrData), .addr(addr), .Data(Data),
                     .memory(memory) );