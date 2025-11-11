// SVA for top_module. Bind this checker to the DUT.
module top_module_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [15:0] in,
  input  logic [1:0]  select,
  input  logic [7:0]  write_addr,
  input  logic [3:0]  write_data,
  input  logic [7:0]  read_addr,
  input  logic [7:0]  out_hi,
  input  logic [7:0]  out_lo,
  input  logic [15:0] bitwise_result,
  input  logic [7:0]  read_data,
  input  logic [3:0]  ram [0:7]
);

  // Reset behavior (not disabled by rst_n)
  assert property (@(posedge clk) !rst_n |-> (out_hi==8'h00 && out_lo==8'h00));

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  function automatic [15:0] be(input [15:0] x, input [1:0] sel);
    unique case (sel)
      2'b00: be = x & (x << 1);
      2'b01: be = x | (x << 1);
      2'b10: be = x ^ (x << 1);
      default: be = x;
    endcase
  endfunction

  logic past_valid;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) past_valid <= 1'b0;
    else        past_valid <= 1'b1;
  end

  // Shadow expected read_data (captures pre-write RAM value)
  logic [7:0] rd_exp;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) rd_exp <= '0;
    else if (read_addr < 8) rd_exp <= {4'h0, ram[read_addr]}; // zero-extend 4->8
    else                    rd_exp <= rd_exp;
  end

  // Bitwise operation correctness
  assert property (bitwise_result == be(in, select));

  // Read path correctness and zero-extension on valid reads
  assert property (read_data == rd_exp);
  assert property ((read_addr < 8) |-> read_data[7:4] == 4'h0);

  // Output packing and one-cycle latency of read_data nibble contribution
  assert property (past_valid |-> (
      out_hi == { be(in,select)[15], be(in,select)[13], be(in,select)[11], be(in,select)[9],
                  $past(rd_exp[3]),  $past(rd_exp[2]),  $past(rd_exp[1]),  $past(rd_exp[0]) } &&
      out_lo == { be(in,select)[14], be(in,select)[12], be(in,select)[10], be(in,select)[8],
                  $past(rd_exp[7]),  $past(rd_exp[6]),  $past(rd_exp[5]),  $past(rd_exp[4]) }
    )
  );

  // RAM write semantics: in-range write updates only targeted element
  assert property ((write_addr < 8) |-> ram[write_addr] == write_data);
  // No unintended writes when in-range (others stable)
  genvar i;
  generate
    for (i=0; i<8; i++) begin : g_stable_others
      assert property ( (write_addr < 8 && write_addr != i) |-> $stable(ram[i]) );
      assert property ( (write_addr >= 8) |-> $stable(ram[i]) );
    end
  endgenerate

  // Read hold when out-of-range
  assert property ((read_addr >= 8) |-> read_data == $past(read_data));

  // Functional coverage
  cover property ($rose(rst_n));
  cover property (select == 2'b00);
  cover property (select == 2'b01);
  cover property (select == 2'b10);
  cover property (select == 2'b11);
  cover property (write_addr < 8);
  cover property (write_addr >= 8);
  cover property (read_addr  < 8);
  cover property (read_addr  >= 8);
  cover property ((read_addr < 8) && (write_addr < 8) && (read_addr == write_addr));
endmodule

// Bind to DUT (connects internal signals too)
bind top_module top_module_sva sva_top (.*,
  .ram(ram),
  .bitwise_result(bitwise_result),
  .read_data(read_data)
);