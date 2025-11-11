// Bind these SVA to the DUT
bind memory_block memory_block_sva mb_sva();

module memory_block_sva;

  // Assume bound into memory_block scope; internal names are visible here
  localparam int DEPTH = 4;
  localparam int DW    = 4;

  // Start guards to allow use of $past safely
  bit started_a, started_b;
  always @(posedge clk_a) started_a <= 1'b1;
  always @(posedge clk_b) started_b <= 1'b1;

  // Lightweight reference model to check DUT behavior (including read-during-write = old data)
  logic [DW-1:0] mem_a_m [0:DEPTH-1];
  logic [DW-1:0] mem_b_m [0:DEPTH-1];
  logic [DW-1:0] dout_a_m, dout_b_m;

  integer ii;
  initial begin
    for (ii = 0; ii < DEPTH; ii++) begin
      mem_a_m[ii] = '0;
      mem_b_m[ii] = '0;
    end
    dout_a_m = '0;
    dout_b_m = '0;
  end

  always @(posedge clk_a) begin
    if (en_a) begin
      if (we_a && addr_a < DEPTH) mem_a_m[addr_a] <= data_a;
      if (addr_a < DEPTH)          dout_a_m        <= mem_a_m[addr_a]; // old data on same-cycle write
    end
  end

  always @(posedge clk_b) begin
    if (en_b) begin
      if (we_b && addr_b < DEPTH) mem_b_m[addr_b] <= data_b;
      if (addr_b < DEPTH)          dout_b_m        <= mem_b_m[addr_b];
    end
  end

  // Basic sanity: address in range and no Xs when enabled
  A_ADDR_RANGE: assert property (@(posedge clk_a) disable iff(!started_a) en_a |-> addr_a < DEPTH);
  B_ADDR_RANGE: assert property (@(posedge clk_b) disable iff(!started_b) en_b |-> addr_b < DEPTH);

  A_NO_X_IN:    assert property (@(posedge clk_a) disable iff(!started_a) en_a |-> !$isunknown({we_a, addr_a, data_a}));
  B_NO_X_IN:    assert property (@(posedge clk_b) disable iff(!started_b) en_b |-> !$isunknown({we_b, addr_b, data_b}));
  A_NO_X_OUT:   assert property (@(posedge clk_a) disable iff(!started_a) en_a |-> !$isunknown(data_out_a));
  B_NO_X_OUT:   assert property (@(posedge clk_b) disable iff(!started_b) en_b |-> !$isunknown(data_out_b));

  // Outputs hold when not enabled
  A_HOLD: assert property (@(posedge clk_a) disable iff(!started_a) !en_a |=> $stable(data_out_a));
  B_HOLD: assert property (@(posedge clk_b) disable iff(!started_b) !en_b |=> $stable(data_out_b));

  // DUT outputs must match the reference model
  A_DOUT_MATCH: assert property (@(posedge clk_a) disable iff(!started_a) data_out_a == dout_a_m);
  B_DOUT_MATCH: assert property (@(posedge clk_b) disable iff(!started_b) data_out_b == dout_b_m);

  // DUT memories must match the reference model (catches write address, old/new data semantics, and unintended writes)
  genvar j;
  generate
    for (j = 0; j < DEPTH; j++) begin : MEM_EQ
      A_MEM_EQ: assert property (@(posedge clk_a) disable iff(!started_a) mem_a[j] == mem_a_m[j]);
      B_MEM_EQ: assert property (@(posedge clk_b) disable iff(!started_b) mem_b[j] == mem_b_m[j]);
    end
  endgenerate

  // Write updates exactly one location, others remain unchanged (explicit one-hot address effect)
  generate
    for (j = 0; j < DEPTH; j++) begin : WR_ONELOC
      A_WR_ONELOC: assert property (@(posedge clk_a) disable iff(!started_a)
                                    en_a && we_a && addr_a < DEPTH |=> mem_a[j] == (j == $past(addr_a) ? $past(data_a) : $past(mem_a[j])));
      B_WR_ONELOC: assert property (@(posedge clk_b) disable iff(!started_b)
                                    en_b && we_b && addr_b < DEPTH |=> mem_b[j] == (j == $past(addr_b) ? $past(data_b) : $past(mem_b[j])));
    end
  endgenerate

  // Functional coverage
  A_COV_WRITE:      cover property (@(posedge clk_a) en_a && we_a && addr_a < DEPTH);
  A_COV_READ:       cover property (@(posedge clk_a) en_a && !we_a && addr_a < DEPTH);
  A_COV_B2B_WR:     cover property (@(posedge clk_a) en_a && we_a ##1 en_a && we_a);
  A_COV_ADDR_CHG:   cover property (@(posedge clk_a) en_a ##1 en_a && addr_a != $past(addr_a));
  A_COV_WR_RD_SAME: cover property (@(posedge clk_a)
                                    en_a && we_a && addr_a < DEPTH ##1
                                    en_a && !we_a && addr_a == $past(addr_a));

  B_COV_WRITE:      cover property (@(posedge clk_b) en_b && we_b && addr_b < DEPTH);
  B_COV_READ:       cover property (@(posedge clk_b) en_b && !we_b && addr_b < DEPTH);
  B_COV_B2B_WR:     cover property (@(posedge clk_b) en_b && we_b ##1 en_b && we_b);
  B_COV_ADDR_CHG:   cover property (@(posedge clk_b) en_b ##1 en_b && addr_b != $past(addr_b));
  B_COV_WR_RD_SAME: cover property (@(posedge clk_b)
                                    en_b && we_b && addr_b < DEPTH ##1
                                    en_b && !we_b && addr_b == $past(addr_b));

endmodule