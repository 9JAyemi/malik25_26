// SVA checker for Computer_Datapath_RegisterFile
// Quality-focused, concise, with functional scoreboard and key coverages

module Computer_Datapath_RegisterFile_sva
  #(parameter WORD_WIDTH = 16,
    parameter DR_WIDTH   = 3)
  ();

  // Access DUT scope (via bind); use DUT signals directly
  // Local decodes (avoid relying on DUT's internal wires)
  wire                  b_CLK = CLK;
  wire                  b_RST = RST;
  wire [WORD_WIDTH-1:0] b_D   = D_bus_in;

  wire                  b_RW  = CNTRL_bus_in[4];
  wire [DR_WIDTH-1:0]   b_DA  = CNTRL_bus_in[19:17];
  wire [DR_WIDTH-1:0]   b_AA  = CNTRL_bus_in[16:14];
  wire [DR_WIDTH-1:0]   b_BA  = CNTRL_bus_in[13:11];

  // Scoreboard
  localparam int DEPTH = (1 << DR_WIDTH);
  logic [WORD_WIDTH-1:0] exp_mem [0:DEPTH-1];
  logic [DEPTH-1:0]      wrote;

  // Update scoreboard on write
  always_ff @(posedge b_CLK or posedge b_RST) begin
    if (b_RST) begin
      wrote <= '0;
    end else if (b_RW) begin
      exp_mem[b_DA] <= b_D;
      wrote[b_DA]   <= 1'b1;
    end
  end

  default clocking cb @ (posedge b_CLK); endclocking
  default disable iff (b_RST);

  // Sanity
  assert property (@cb !$isunknown({b_RW, b_DA, b_AA, b_BA}));
  assert property (@cb b_RW |-> !$isunknown(b_D));

  // Read correctness for any address that has been written
  assert property (@cb wrote[b_AA] |-> (ADDR_bus_out == exp_mem[b_AA]));
  assert property (@cb wrote[b_BA] |-> (B_data_out    == exp_mem[b_BA]));

  // RAW (write -> next-cycle read of same address returns last D)
  assert property (@cb b_RW ##1 (b_AA == $past(b_DA)) |-> (ADDR_bus_out == $past(b_D)));
  assert property (@cb b_RW ##1 (b_BA == $past(b_DA)) |-> (B_data_out    == $past(b_D)));

  // Both ports reading same (written) address must match
  assert property (@cb (wrote[b_AA] && (b_AA == b_BA)) |-> (ADDR_bus_out == B_data_out));

  // Outputs remain stable if address stable and no write hits that address
  assert property (@cb $stable(b_AA) && !(b_RW && (b_DA == b_AA)) |-> $stable(ADDR_bus_out));
  assert property (@cb $stable(b_BA) && !(b_RW && (b_DA == b_BA)) |-> $stable(B_data_out));

  // No spurious change when writing another address
  assert property (@cb $stable(b_AA) && b_RW && (b_DA != b_AA) |-> $stable(ADDR_bus_out));
  assert property (@cb $stable(b_BA) && b_RW && (b_DA != b_BA) |-> $stable(B_data_out));

  // Outputs known when reading a written location
  assert property (@cb wrote[b_AA] |-> !$isunknown(ADDR_bus_out));
  assert property (@cb wrote[b_BA] |-> !$isunknown(B_data_out));

  // Coverage
  cover property (@cb b_RW);                 // see writes
  cover property (@cb !b_RW);                // see non-writes
  // RAW hazards observed on each port
  cover property (@cb b_RW ##1 (b_AA == $past(b_DA)));
  cover property (@cb b_RW ##1 (b_BA == $past(b_DA)));
  // Same-address dual read after write
  cover property (@cb b_RW ##1 (b_AA == $past(b_DA) && b_BA == $past(b_DA)));
  // Per-address write and subsequent reads
  genvar a;
  generate
    for (a = 0; a < DEPTH; a++) begin : COV_ADDR
      cover property (@cb b_RW && (b_DA == a));
      cover property (@cb b_RW && (b_DA == a) ##1 (b_AA == a));
      cover property (@cb b_RW && (b_DA == a) ##1 (b_BA == a));
    end
  endgenerate

endmodule

bind Computer_Datapath_RegisterFile
  Computer_Datapath_RegisterFile_sva #(.WORD_WIDTH(WORD_WIDTH),
                                       .DR_WIDTH  (DR_WIDTH)) sva_inst();