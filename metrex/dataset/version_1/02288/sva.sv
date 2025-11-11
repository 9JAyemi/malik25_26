// SVA for softusb_timer
// Bind this file to the DUT. Focused, concise checks + useful coverage.

module softusb_timer_sva(
  input logic        usb_clk,
  input logic        usb_rst,
  input logic        io_we,
  input logic [5:0]  io_a,
  input logic [7:0]  io_do,
  input logic [31:0] counter
);

  // Helper: address decode
  function automatic bit is_timer_addr(input logic [5:0] a);
    return (a inside {6'h20,6'h21,6'h22,6'h23});
  endfunction

  default clocking cb @(posedge usb_clk); endclocking

  // Reset behavior: next-cycle zero and hold while asserted
  assert property (usb_rst |=> (counter==32'd0 && io_do==8'd0));
  assert property (usb_rst && $past(usb_rst) |-> (counter==32'd0 && io_do==8'd0));

  // Counter next-state: write to any timer address clears; otherwise increments
  assert property (!$past(usb_rst) && $past(io_we) && is_timer_addr($past(io_a)) |-> counter==32'd0);
  assert property (!$past(usb_rst) && !($past(io_we) && is_timer_addr($past(io_a))) |-> counter==$past(counter)+32'd1);

  // Read data muxing (io_do reflects previous counter slice based on previous address)
  assert property (!$past(usb_rst) && ($past(io_a)==6'h20) |-> io_do==$past(counter[7:0]));
  assert property (!$past(usb_rst) && ($past(io_a)==6'h21) |-> io_do==$past(counter[15:8]));
  assert property (!$past(usb_rst) && ($past(io_a)==6'h22) |-> io_do==$past(counter[23:16]));
  assert property (!$past(usb_rst) && ($past(io_a)==6'h23) |-> io_do==$past(counter[31:24]));
  assert property (!$past(usb_rst) && !is_timer_addr($past(io_a)) |-> io_do==8'h00);

  // Optional sanity: outputs/state known when not in reset
  assert property (!usb_rst |-> !$isunknown(io_do));
  assert property (!usb_rst |-> !$isunknown(counter));

  // --------------------------------------------------------------------------
  // Coverage
  // Read each byte
  cover property (!$past(usb_rst) && ($past(io_a)==6'h20) && (io_do==$past(counter[7:0])));
  cover property (!$past(usb_rst) && ($past(io_a)==6'h21) && (io_do==$past(counter[15:8])));
  cover property (!$past(usb_rst) && ($past(io_a)==6'h22) && (io_do==$past(counter[23:16])));
  cover property (!$past(usb_rst) && ($past(io_a)==6'h23) && (io_do==$past(counter[31:24])));

  // Write-induced counter clear
  cover property (!$past(usb_rst) && $past(io_we) && is_timer_addr($past(io_a)) && (counter==32'd0));

  // Natural increment (and implicit wrap)
  cover property (!$past(usb_rst) && !($past(io_we) && is_timer_addr($past(io_a))) && counter==$past(counter)+32'd1);
  cover property (!$past(usb_rst) && !($past(io_we) && is_timer_addr($past(io_a))) &&
                  ($past(counter)==32'hFFFF_FFFF) && (counter==32'd0));

endmodule

bind softusb_timer softusb_timer_sva sva (
  .usb_clk(usb_clk),
  .usb_rst(usb_rst),
  .io_we(io_we),
  .io_a(io_a),
  .io_do(io_do),
  .counter(counter)
);