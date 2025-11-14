// SVA checkers for altera_onchip_flash_* modules (concise, quality-focused)

// Address range check
module sva_altera_onchip_flash_address_range_check
  #(parameter FLASH_ADDR_WIDTH = 23,
    parameter MIN_VALID_ADDR   = 1,
    parameter MAX_VALID_ADDR   = 1)
  (input  [FLASH_ADDR_WIDTH-1:0] address,
   input                         is_addr_within_valid_range);

  // Functional equivalence
  assert property (@($changed(address))
    is_addr_within_valid_range == ((address >= MIN_VALID_ADDR) && (address <= MAX_VALID_ADDR)));

  // Sanity
  assert property (@($changed(address)) !$isunknown(is_addr_within_valid_range));

  // Coverage
  cover property (@($changed(address)) (address == MIN_VALID_ADDR) && is_addr_within_valid_range);
  cover property (@($changed(address)) (address == MAX_VALID_ADDR) && is_addr_within_valid_range);
  cover property (@($changed(address)) (address <  MIN_VALID_ADDR) && !is_addr_within_valid_range);
  cover property (@($changed(address)) (address >  MAX_VALID_ADDR) && !is_addr_within_valid_range);
endmodule

bind altera_onchip_flash_address_range_check
  sva_altera_onchip_flash_address_range_check
  #(.FLASH_ADDR_WIDTH(FLASH_ADDR_WIDTH),
    .MIN_VALID_ADDR(MIN_VALID_ADDR),
    .MAX_VALID_ADDR(MAX_VALID_ADDR))
  u_sva (.address(address), .is_addr_within_valid_range(is_addr_within_valid_range));


// Address write protection check (sector index or address ranges)
module sva_altera_onchip_flash_address_write_protection_check
  #(parameter FLASH_ADDR_WIDTH = 23,
    parameter SECTOR1_START_ADDR = 1, parameter SECTOR1_END_ADDR = 1,
    parameter SECTOR2_START_ADDR = 1, parameter SECTOR2_END_ADDR = 1,
    parameter SECTOR3_START_ADDR = 1, parameter SECTOR3_END_ADDR = 1,
    parameter SECTOR4_START_ADDR = 1, parameter SECTOR4_END_ADDR = 1,
    parameter SECTOR5_START_ADDR = 1, parameter SECTOR5_END_ADDR = 1,
    parameter SECTOR_READ_PROTECTION_MODE = 5'b11111)
  (input                         use_sector_addr,
   input      [FLASH_ADDR_WIDTH-1:0] address,
   input      [4:0]              write_protection_mode,
   input                         is_addr_writable);

  // Recompute expected sector matches and writability
  wire s1a = use_sector_addr ? (address==1) : ((address>=SECTOR1_START_ADDR)&&(address<=SECTOR1_END_ADDR));
  wire s2a = use_sector_addr ? (address==2) : ((address>=SECTOR2_START_ADDR)&&(address<=SECTOR2_END_ADDR));
  wire s3a = use_sector_addr ? (address==3) : ((address>=SECTOR3_START_ADDR)&&(address<=SECTOR3_END_ADDR));
  wire s4a = use_sector_addr ? (address==4) : ((address>=SECTOR4_START_ADDR)&&(address<=SECTOR4_END_ADDR));
  wire s5a = use_sector_addr ? (address==5) : ((address>=SECTOR5_START_ADDR)&&(address<=SECTOR5_END_ADDR));
  wire s1w = ~(write_protection_mode[0] || SECTOR_READ_PROTECTION_MODE[0]);
  wire s2w = ~(write_protection_mode[1] || SECTOR_READ_PROTECTION_MODE[1]);
  wire s3w = ~(write_protection_mode[2] || SECTOR_READ_PROTECTION_MODE[2]);
  wire s4w = ~(write_protection_mode[3] || SECTOR_READ_PROTECTION_MODE[3]);
  wire s5w = ~(write_protection_mode[4] || SECTOR_READ_PROTECTION_MODE[4]);
  wire exp_w = (s1w && s1a) || (s2w && s2a) || (s3w && s3a) || (s4w && s4a) || (s5w && s5a);

  // Functional equivalence and sanity
  assert property (@($changed({use_sector_addr,address,write_protection_mode}))
                   is_addr_writable == exp_w);
  assert property (@($changed({use_sector_addr,address,write_protection_mode}))
                   !$isunknown(is_addr_writable));

  // One-hot of sector match in sector-index mode
  assert property (@($changed({use_sector_addr,address}))
                   use_sector_addr && (address inside {[1:5]})
                   |-> $onehot({s1a,s2a,s3a,s4a,s5a}));

  // Writability bit meaning
  assert property (@($changed(write_protection_mode)) (write_protection_mode[0] || SECTOR_READ_PROTECTION_MODE[0]) |-> !s1w);
  assert property (@($changed(write_protection_mode)) (write_protection_mode[1] || SECTOR_READ_PROTECTION_MODE[1]) |-> !s2w);
  assert property (@($changed(write_protection_mode)) (write_protection_mode[2] || SECTOR_READ_PROTECTION_MODE[2]) |-> !s3w);
  assert property (@($changed(write_protection_mode)) (write_protection_mode[3] || SECTOR_READ_PROTECTION_MODE[3]) |-> !s4w);
  assert property (@($changed(write_protection_mode)) (write_protection_mode[4] || SECTOR_READ_PROTECTION_MODE[4]) |-> !s5w);
  assert property (@($changed(write_protection_mode)) (!write_protection_mode[0] && !SECTOR_READ_PROTECTION_MODE[0]) |-> s1w);
  assert property (@($changed(write_protection_mode)) (!write_protection_mode[1] && !SECTOR_READ_PROTECTION_MODE[1]) |-> s2w);
  assert property (@($changed(write_protection_mode)) (!write_protection_mode[2] && !SECTOR_READ_PROTECTION_MODE[2]) |-> s3w);
  assert property (@($changed(write_protection_mode)) (!write_protection_mode[3] && !SECTOR_READ_PROTECTION_MODE[3]) |-> s4w);
  assert property (@($changed(write_protection_mode)) (!write_protection_mode[4] && !SECTOR_READ_PROTECTION_MODE[4]) |-> s5w);

  // Coverage: each sector selected + writable/not writable, both addr modes; and none-selected path
  cover property (@($changed({use_sector_addr,address,write_protection_mode})) s1a &&  s1w && is_addr_writable);
  cover property (@($changed({use_sector_addr,address,write_protection_mode})) s1a && !s1w && !is_addr_writable);
  cover property (@($changed({use_sector_addr,address,write_protection_mode})) s2a &&  s2w && is_addr_writable);
  cover property (@($changed({use_sector_addr,address,write_protection_mode})) s2a && !s2w && !is_addr_writable);
  cover property (@($changed({use_sector_addr,address,write_protection_mode})) s3a &&  s3w && is_addr_writable);
  cover property (@($changed({use_sector_addr,address,write_protection_mode})) s3a && !s3w && !is_addr_writable);
  cover property (@($changed({use_sector_addr,address,write_protection_mode})) s4a &&  s4w && is_addr_writable);
  cover property (@($changed({use_sector_addr,address,write_protection_mode})) s4a && !s4w && !is_addr_writable);
  cover property (@($changed({use_sector_addr,address,write_protection_mode})) s5a &&  s5w && is_addr_writable);
  cover property (@($changed({use_sector_addr,address,write_protection_mode})) s5a && !s5w && !is_addr_writable);
  cover property (@($changed({use_sector_addr,address,write_protection_mode})) !(s1a||s2a||s3a||s4a||s5a) && !is_addr_writable);
endmodule

bind altera_onchip_flash_address_write_protection_check
  sva_altera_onchip_flash_address_write_protection_check
  #(.FLASH_ADDR_WIDTH(FLASH_ADDR_WIDTH),
    .SECTOR1_START_ADDR(SECTOR1_START_ADDR), .SECTOR1_END_ADDR(SECTOR1_END_ADDR),
    .SECTOR2_START_ADDR(SECTOR2_START_ADDR), .SECTOR2_END_ADDR(SECTOR2_END_ADDR),
    .SECTOR3_START_ADDR(SECTOR3_START_ADDR), .SECTOR3_END_ADDR(SECTOR3_END_ADDR),
    .SECTOR4_START_ADDR(SECTOR4_START_ADDR), .SECTOR4_END_ADDR(SECTOR4_END_ADDR),
    .SECTOR5_START_ADDR(SECTOR5_START_ADDR), .SECTOR5_END_ADDR(SECTOR5_END_ADDR),
    .SECTOR_READ_PROTECTION_MODE(SECTOR_READ_PROTECTION_MODE))
  u_sva (.use_sector_addr(use_sector_addr),
         .address(address),
         .write_protection_mode(write_protection_mode),
         .is_addr_writable(is_addr_writable));


// Sector-index write protection check (3-bit sector id)
module sva_altera_onchip_flash_s_address_write_protection_check
  (input [2:0] address,
   input       is_sector1_writable,
   input       is_sector2_writable,
   input       is_sector3_writable,
   input       is_sector4_writable,
   input       is_sector5_writable,
   input       is_addr_writable);

  wire s1a = (address==3'd1);
  wire s2a = (address==3'd2);
  wire s3a = (address==3'd3);
  wire s4a = (address==3'd4);
  wire s5a = (address==3'd5);
  wire exp_w = (is_sector1_writable && s1a) ||
               (is_sector2_writable && s2a) ||
               (is_sector3_writable && s3a) ||
               (is_sector4_writable && s4a) ||
               (is_sector5_writable && s5a);

  assert property (@($changed({address,is_sector1_writable,is_sector2_writable,is_sector3_writable,is_sector4_writable,is_sector5_writable}))
                   is_addr_writable == exp_w);
  assert property (@($changed(address)) $onehot0({s1a,s2a,s3a,s4a,s5a}));
  assert property (@($changed({address,is_sector1_writable,is_sector2_writable,is_sector3_writable,is_sector4_writable,is_sector5_writable}))
                   !$isunknown(is_addr_writable));

  // Coverage: each sector chosen and writable/not writable, plus default (0 or >5)
  cover property (@($changed({address,is_sector1_writable})) (address==3'd1) &&  is_sector1_writable && is_addr_writable);
  cover property (@($changed({address,is_sector1_writable})) (address==3'd1) && !is_sector1_writable && !is_addr_writable);
  cover property (@($changed({address,is_sector2_writable})) (address==3'd2) &&  is_sector2_writable && is_addr_writable);
  cover property (@($changed({address,is_sector2_writable})) (address==3'd2) && !is_sector2_writable && !is_addr_writable);
  cover property (@($changed({address,is_sector3_writable})) (address==3'd3) &&  is_sector3_writable && is_addr_writable);
  cover property (@($changed({address,is_sector3_writable})) (address==3'd3) && !is_sector3_writable && !is_addr_writable);
  cover property (@($changed({address,is_sector4_writable})) (address==3'd4) &&  is_sector4_writable && is_addr_writable);
  cover property (@($changed({address,is_sector4_writable})) (address==3'd4) && !is_sector4_writable && !is_addr_writable);
  cover property (@($changed({address,is_sector5_writable})) (address==3'd5) &&  is_sector5_writable && is_addr_writable);
  cover property (@($changed({address,is_sector5_writable})) (address==3'd5) && !is_sector5_writable && !is_addr_writable);
  cover property (@($changed(address)) !(address inside {3'd1,3'd2,3'd3,3'd4,3'd5}) && !is_addr_writable);
endmodule

bind altera_onchip_flash_s_address_write_protection_check
  sva_altera_onchip_flash_s_address_write_protection_check
  u_sva (.address(address),
         .is_sector1_writable(is_sector1_writable),
         .is_sector2_writable(is_sector2_writable),
         .is_sector3_writable(is_sector3_writable),
         .is_sector4_writable(is_sector4_writable),
         .is_sector5_writable(is_sector5_writable),
         .is_addr_writable(is_addr_writable));


// Address-range write protection check (full address ranges)
module sva_altera_onchip_flash_a_address_write_protection_check
  #(parameter FLASH_ADDR_WIDTH = 23,
    parameter SECTOR1_START_ADDR = 1, parameter SECTOR1_END_ADDR = 1,
    parameter SECTOR2_START_ADDR = 1, parameter SECTOR2_END_ADDR = 1,
    parameter SECTOR3_START_ADDR = 1, parameter SECTOR3_END_ADDR = 1,
    parameter SECTOR4_START_ADDR = 1, parameter SECTOR4_END_ADDR = 1,
    parameter SECTOR5_START_ADDR = 1, parameter SECTOR5_END_ADDR = 1)
  (input [FLASH_ADDR_WIDTH-1:0] address,
   input is_sector1_writable,
   input is_sector2_writable,
   input is_sector3_writable,
   input is_sector4_writable,
   input is_sector5_writable,
   input is_addr_writable);

  wire s1a = ((address>=SECTOR1_START_ADDR)&&(address<=SECTOR1_END_ADDR));
  wire s2a = ((address>=SECTOR2_START_ADDR)&&(address<=SECTOR2_END_ADDR));
  wire s3a = ((address>=SECTOR3_START_ADDR)&&(address<=SECTOR3_END_ADDR));
  wire s4a = ((address>=SECTOR4_START_ADDR)&&(address<=SECTOR4_END_ADDR));
  wire s5a = ((address>=SECTOR5_START_ADDR)&&(address<=SECTOR5_END_ADDR));
  wire exp_w = (is_sector1_writable && s1a) ||
               (is_sector2_writable && s2a) ||
               (is_sector3_writable && s3a) ||
               (is_sector4_writable && s4a) ||
               (is_sector5_writable && s5a);

  assert property (@($changed({address,is_sector1_writable,is_sector2_writable,is_sector3_writable,is_sector4_writable,is_sector5_writable}))
                   is_addr_writable == exp_w);
  assert property (@($changed({address,is_sector1_writable,is_sector2_writable,is_sector3_writable,is_sector4_writable,is_sector5_writable}))
                   !$isunknown(is_addr_writable));

  // Coverage: each sector-range selected with writable and not writable; and address not in any sector
  cover property (@($changed({address,is_sector1_writable})) s1a &&  is_sector1_writable && is_addr_writable);
  cover property (@($changed({address,is_sector1_writable})) s1a && !is_sector1_writable && !is_addr_writable);
  cover property (@($changed({address,is_sector2_writable})) s2a &&  is_sector2_writable && is_addr_writable);
  cover property (@($changed({address,is_sector2_writable})) s2a && !is_sector2_writable && !is_addr_writable);
  cover property (@($changed({address,is_sector3_writable})) s3a &&  is_sector3_writable && is_addr_writable);
  cover property (@($changed({address,is_sector3_writable})) s3a && !is_sector3_writable && !is_addr_writable);
  cover property (@($changed({address,is_sector4_writable})) s4a &&  is_sector4_writable && is_addr_writable);
  cover property (@($changed({address,is_sector4_writable})) s4a && !is_sector4_writable && !is_addr_writable);
  cover property (@($changed({address,is_sector5_writable})) s5a &&  is_sector5_writable && is_addr_writable);
  cover property (@($changed({address,is_sector5_writable})) s5a && !is_sector5_writable && !is_addr_writable);
  cover property (@($changed(address)) !(s1a||s2a||s3a||s4a||s5a) && !is_addr_writable);
endmodule

bind altera_onchip_flash_a_address_write_protection_check
  sva_altera_onchip_flash_a_address_write_protection_check
  #(.FLASH_ADDR_WIDTH(FLASH_ADDR_WIDTH),
    .SECTOR1_START_ADDR(SECTOR1_START_ADDR), .SECTOR1_END_ADDR(SECTOR1_END_ADDR),
    .SECTOR2_START_ADDR(SECTOR2_START_ADDR), .SECTOR2_END_ADDR(SECTOR2_END_ADDR),
    .SECTOR3_START_ADDR(SECTOR3_START_ADDR), .SECTOR3_END_ADDR(SECTOR3_END_ADDR),
    .SECTOR4_START_ADDR(SECTOR4_START_ADDR), .SECTOR4_END_ADDR(SECTOR4_END_ADDR),
    .SECTOR5_START_ADDR(SECTOR5_START_ADDR), .SECTOR5_END_ADDR(SECTOR5_END_ADDR))
  u_sva (.address(address),
         .is_sector1_writable(is_sector1_writable),
         .is_sector2_writable(is_sector2_writable),
         .is_sector3_writable(is_sector3_writable),
         .is_sector4_writable(is_sector4_writable),
         .is_sector5_writable(is_sector5_writable),
         .is_addr_writable(is_addr_writable));


// Convert address
module sva_altera_onchip_flash_convert_address
  #(parameter FLASH_ADDR_WIDTH = 23,
    parameter ADDR_RANGE1_END_ADDR = 1,
    parameter ADDR_RANGE1_OFFSET   = 1,
    parameter ADDR_RANGE2_OFFSET   = 1)
  (input  [FLASH_ADDR_WIDTH-1:0] address,
   input  [FLASH_ADDR_WIDTH-1:0] flash_addr);

  wire [FLASH_ADDR_WIDTH-1:0] off1 = ADDR_RANGE1_OFFSET[FLASH_ADDR_WIDTH-1:0];
  wire [FLASH_ADDR_WIDTH-1:0] off2 = ADDR_RANGE2_OFFSET[FLASH_ADDR_WIDTH-1:0];
  wire [FLASH_ADDR_WIDTH-1:0] end1 = ADDR_RANGE1_END_ADDR[FLASH_ADDR_WIDTH-1:0];
  wire [FLASH_ADDR_WIDTH-1:0] exp  = (address <= end1) ? (address + off1) : (address + off2);

  assert property (@($changed(address)) flash_addr == exp);
  assert property (@($changed(address)) !$isunknown(flash_addr));

  // Coverage: both ranges and boundary
  cover property (@($changed(address)) (address <  end1) && (flash_addr == address + off1));
  cover property (@($changed(address)) (address == end1) && (flash_addr == address + off1));
  cover property (@($changed(address)) (address >  end1) && (flash_addr == address + off2));
endmodule

bind altera_onchip_flash_convert_address
  sva_altera_onchip_flash_convert_address
  #(.FLASH_ADDR_WIDTH(FLASH_ADDR_WIDTH),
    .ADDR_RANGE1_END_ADDR(ADDR_RANGE1_END_ADDR),
    .ADDR_RANGE1_OFFSET(ADDR_RANGE1_OFFSET),
    .ADDR_RANGE2_OFFSET(ADDR_RANGE2_OFFSET))
  u_sva (.address(address), .flash_addr(flash_addr));


// Convert sector
module sva_altera_onchip_flash_convert_sector
  #(parameter SECTOR1_MAP = 1,
    parameter SECTOR2_MAP = 1,
    parameter SECTOR3_MAP = 1,
    parameter SECTOR4_MAP = 1,
    parameter SECTOR5_MAP = 1)
  (input  [2:0] sector,
   input  [2:0] flash_sector);

  wire [2:0] m1 = SECTOR1_MAP[2:0];
  wire [2:0] m2 = SECTOR2_MAP[2:0];
  wire [2:0] m3 = SECTOR3_MAP[2:0];
  wire [2:0] m4 = SECTOR4_MAP[2:0];
  wire [2:0] m5 = SECTOR5_MAP[2:0];
  wire [2:0] exp = (sector==3'd1) ? m1 :
                   (sector==3'd2) ? m2 :
                   (sector==3'd3) ? m3 :
                   (sector==3'd4) ? m4 :
                   (sector==3'd5) ? m5 : 3'd0;

  assert property (@($changed(sector)) flash_sector == exp);
  assert property (@($changed(sector)) !$isunknown(flash_sector));

  // Coverage: each mapping and default
  cover property (@($changed(sector)) sector==3'd1 && (flash_sector==m1));
  cover property (@($changed(sector)) sector==3'd2 && (flash_sector==m2));
  cover property (@($changed(sector)) sector==3'd3 && (flash_sector==m3));
  cover property (@($changed(sector)) sector==3'd4 && (flash_sector==m4));
  cover property (@($changed(sector)) sector==3'd5 && (flash_sector==m5));
  cover property (@($changed(sector)) !(sector inside {3'd1,3'd2,3'd3,3'd4,3'd5}) && (flash_sector==3'd0));
endmodule

bind altera_onchip_flash_convert_sector
  sva_altera_onchip_flash_convert_sector
  #(.SECTOR1_MAP(SECTOR1_MAP),
    .SECTOR2_MAP(SECTOR2_MAP),
    .SECTOR3_MAP(SECTOR3_MAP),
    .SECTOR4_MAP(SECTOR4_MAP),
    .SECTOR5_MAP(SECTOR5_MAP))
  u_sva (.sector(sector), .flash_sector(flash_sector));


// Counter
module sva_altera_onchip_flash_counter
  (input clock, input reset, input [4:0] count);
  // Async reset drives count to 0 immediately (NBA delay accounted with ##0)
  assert property (@(posedge reset) ##0 (count==5'd0));

  // Reset dominates on clock edge
  assert property (@(posedge clock) reset |-> (count==5'd0));

  // Increment when not in reset and previous cycle not in reset
  assert property (@(posedge clock) (!reset && !$past(reset)) |-> (count == $past(count)+5'd1));

  // No X on count
  assert property (@(posedge clock or posedge reset) !$isunknown(count));

  // Coverage: observe reset pulse and wrap-around 31->0
  cover property (@(posedge clock) $rose(reset));
  cover property (@(posedge clock) (!reset && !$past(reset) && ($past(count)==5'd31) && (count==5'd0)));
endmodule

bind altera_onchip_flash_counter
  sva_altera_onchip_flash_counter
  u_sva (.clock(clock), .reset(reset), .count(count));