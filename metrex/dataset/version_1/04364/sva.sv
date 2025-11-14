// SVA for sector_to_flash_map
// Bind this module to the DUT and connect a sampling clock.

module sector_to_flash_map_sva #(
  parameter logic [2:0] SECTOR1_MAP = 3'b001,
  parameter logic [2:0] SECTOR2_MAP = 3'b010,
  parameter logic [2:0] SECTOR3_MAP = 3'b011,
  parameter logic [2:0] SECTOR4_MAP = 3'b100,
  parameter logic [2:0] SECTOR5_MAP = 3'b101
)(
  input  logic        clk,
  input  logic [2:0]  sector,
  input  logic [2:0]  flash_sector
);

  default clocking cb @(posedge clk); endclocking

  function automatic logic [2:0] ref_map (logic [2:0] s);
    case (s)
      3'd1: ref_map = SECTOR1_MAP;
      3'd2: ref_map = SECTOR2_MAP;
      3'd3: ref_map = SECTOR3_MAP;
      3'd4: ref_map = SECTOR4_MAP;
      3'd5: ref_map = SECTOR5_MAP;
      default: ref_map = 3'd0;
    endcase
  endfunction

  // Functional correctness: flash_sector must equal the reference mapping
  ap_map:    assert property (flash_sector == ref_map(sector));

  // No X/Z propagation when input is known
  ap_known:  assert property (!$isunknown(sector) |-> !$isunknown(flash_sector));

  // Combinational behavior: if input is stable across cycles, output is stable
  ap_stable: assert property ($stable(sector) |-> $stable(flash_sector));

  // Coverage: hit each case arm including default for 0,6,7
  cp_s0: cover property (sector==3'd0 && flash_sector==3'd0);
  cp_s1: cover property (sector==3'd1 && flash_sector==SECTOR1_MAP);
  cp_s2: cover property (sector==3'd2 && flash_sector==SECTOR2_MAP);
  cp_s3: cover property (sector==3'd3 && flash_sector==SECTOR3_MAP);
  cp_s4: cover property (sector==3'd4 && flash_sector==SECTOR4_MAP);
  cp_s5: cover property (sector==3'd5 && flash_sector==SECTOR5_MAP);
  cp_s6: cover property (sector==3'd6 && flash_sector==3'd0);
  cp_s7: cover property (sector==3'd7 && flash_sector==3'd0);

endmodule

// Example bind (connect an appropriate clock from your environment):
// bind sector_to_flash_map sector_to_flash_map_sva #(
//   .SECTOR1_MAP(SECTOR1_MAP), .SECTOR2_MAP(SECTOR2_MAP),
//   .SECTOR3_MAP(SECTOR3_MAP), .SECTOR4_MAP(SECTOR4_MAP),
//   .SECTOR5_MAP(SECTOR5_MAP)
// ) sva_i ( .clk(tb_clk), .sector(sector), .flash_sector(flash_sector) );