// SVA for store_data_translator
// Bind this module to the DUT and provide a sampling clock/reset.
// Example:
// bind store_data_translator store_data_translator_sva #(.WIDTH(WIDTH)) sva (.*, .clk(tb_clk), .rst_n(tb_rst_n));

module store_data_translator_sva #(
  parameter int WIDTH = 32
)(
  input  logic                   clk,
  input  logic                   rst_n,
  input  logic [WIDTH-1:0]       write_data,
  input  logic [1:0]             d_address,
  input  logic [1:0]             store_size,
  input  logic [3:0]             d_byteena,
  input  logic [WIDTH-1:0]       d_writedataout
);

  // This design’s RTL hardcodes 24/16/8 zero-extends; assert WIDTH=32 for correctness.
  initial assert (WIDTH == 32)
    else $fatal(1, "store_data_translator_sva assumes WIDTH==32");

  // Helpers
  function automatic [3:0] exp_be(input logic [1:0] sz, input logic [1:0] addr);
    case (sz)
      2'b11: exp_be = 4'b1000 >> addr;                // byte
      2'b01: exp_be = addr[1] ? 4'b0011 : 4'b1100;    // half
      default: exp_be = 4'b1111;                      // word/others
    endcase
  endfunction

  function automatic [31:0] be2mask(input logic [3:0] be);
    be2mask = { {8{be[3]}}, {8{be[2]}}, {8{be[1]}}, {8{be[0]}} };
  endfunction

  function automatic [31:0] exp_data(input logic [31:0] wd, input logic [1:0] sz, input logic [1:0] addr);
    case (sz)
      2'b11: exp_data = (wd[7:0]  << (8*(3-addr)));          // byte lane
      2'b01: exp_data = (wd[15:0] << (addr[1] ? 0 : 16));     // half lane
      default: exp_data = wd;                                 // word
    endcase
  endfunction

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Functional mapping: byte enables and data placement
  assert property (1 |-> (d_byteena == exp_be(store_size, d_address) &&
                          d_writedataout[31:0] == exp_data(write_data[31:0], store_size, d_address)));

  // Shape/legality of byte enables per size
  assert property ((store_size == 2'b11) |-> $onehot(d_byteena));                // byte
  assert property ((store_size == 2'b01) |-> (d_byteena inside {4'b1100,4'b0011})); // half
  assert property (((store_size != 2'b11) && (store_size != 2'b01)) |-> (d_byteena == 4'b1111)); // word/others

  // Output bytes must be zero where byteena deasserted
  assert property (1 |-> ( (d_writedataout[31:0] & ~be2mask(d_byteena)) == 32'b0 ));

  // No X/Z on outputs when inputs are known
  assert property ( (! $isunknown({write_data, d_address, store_size})) |-> ! $isunknown({d_byteena, d_writedataout}) );

  // Coverage: exercise all cases/lanes
  cover property (store_size == 2'b11 && d_address == 2'd0);
  cover property (store_size == 2'b11 && d_address == 2'd1);
  cover property (store_size == 2'b11 && d_address == 2'd2);
  cover property (store_size == 2'b11 && d_address == 2'd3);

  cover property (store_size == 2'b01 && d_address[1] == 1'b0); // upper half
  cover property (store_size == 2'b01 && d_address[1] == 1'b1); // lower half

  cover property (store_size == 2'b00);
  cover property (store_size == 2'b10);

endmodule