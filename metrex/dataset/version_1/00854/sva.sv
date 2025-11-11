// SVA for vga_address_translator
// Bind this file after DUT is compiled.

module vga_address_translator_asserts #(
  parameter string RESOLUTION = "320x240"
)(
  input  logic [((RESOLUTION=="320x240")?8:7):0]  x,
  input  logic [((RESOLUTION=="320x240")?7:6):0]  y,
  input  logic [((RESOLUTION=="320x240")?16:14):0] mem_address
);

  localparam bit IS_320 = (RESOLUTION == "320x240");
  localparam int M      = IS_320 ? 320 : 160;
  localparam int MAX_X  = IS_320 ? 319 : 159;
  localparam int MAX_Y  = IS_320 ? 239 : 119;
  localparam int AW     = IS_320 ? 17  : 15;

  default clocking cb @(x or y or mem_address); endclocking

  function automatic logic [AW-1:0] exp_addr(input logic [$bits(x)-1:0] xi,
                                             input logic [$bits(y)-1:0] yi);
    logic [16:0] a320;
    logic [15:0] a160;
    if (IS_320) begin
      a320 = {1'b0, yi, 8'd0} + {1'b0, yi, 6'd0} + {1'b0, xi};
      exp_addr = a320;
    end else begin
      a160 = {1'b0, yi, 7'd0} + {1'b0, yi, 5'd0} + {1'b0, xi};
      exp_addr = a160[14:0];
    end
  endfunction

  // Core functional check
  assert property (mem_address == exp_addr(x,y))
    else $error("vga_address_translator: address map mismatch");

  // Known-ness propagation
  assert property (!$isunknown({x,y}) |-> !$isunknown(mem_address))
    else $error("vga_address_translator: mem_address X/Z with known inputs");

  // Simple boundaries
  assert property (y == '0 |-> mem_address == x);
  assert property (x == '0 |-> mem_address == exp_addr('0,y));

  // Monotonicity
  assert property ($stable(y) && (x == $past(x)+1) |-> mem_address == $past(mem_address)+1);
  assert property ($stable(x) && (y == $past(y)+1) |-> mem_address == $past(mem_address)+M);

  // No output glitches without input changes
  assert property ($stable(x) && $stable(y) |-> $stable(mem_address))
    else $error("vga_address_translator: mem_address changed without x/y");

  // Range under legal coordinates
  assert property ((x <= MAX_X && y <= MAX_Y) |-> mem_address <= (MAX_Y*M + MAX_X));

  // Coverage
  cover property (x==0 && y==0 && mem_address==0);
  cover property (x==MAX_X && y==0 && mem_address==MAX_X);
  cover property (x==0 && y==MAX_Y && mem_address==(MAX_Y*M));
  cover property (x==MAX_X && y==MAX_Y && mem_address==(MAX_Y*M+MAX_X));
  cover property ($stable(y) && (x == $past(x)+1));
  cover property ($stable(x) && (y == $past(y)+1));

endmodule

bind vga_address_translator
  vga_address_translator_asserts #(.RESOLUTION(RESOLUTION)))
  vga_address_translator_asserts_i (.x(x), .y(y), .mem_address(mem_address));