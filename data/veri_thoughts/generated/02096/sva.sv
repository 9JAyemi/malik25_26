module mux_parity_sva (
  input logic clk,
  input logic [2:0] sel,
  input logic [3:0] data0,
  input logic [3:0] data1,
  input logic [3:0] data2,
  input logic [3:0] data3,
  input logic [3:0] data4,
  input logic [3:0] data5,
  input logic [3:0] out,
  input logic parity
);

  // Mux output equals sum-of-products of data inputs gated by sel
  check_mux_sum_of_products: assert property (
    @(posedge clk)
      out == (
        ((sel == 3'b000) ? data0 : 4'b0) |
        ((sel == 3'b001) ? data1 : 4'b0) |
        ((sel == 3'b010) ? data2 : 4'b0) |
        ((sel == 3'b011) ? data3 : 4'b0) |
        ((sel == 3'b100) ? data4 : 4'b0) |
        ((sel == 3'b101) ? data5 : 4'b0)
      )
  );

  // When sel=000, out equals data0
  check_sel0_route: assert property (
    @(posedge clk) (sel == 3'b000) |-> (out == data0)
  );

  // When sel=001, out equals data1
  check_sel1_route: assert property (
    @(posedge clk) (sel == 3'b001) |-> (out == data1)
  );

  // When sel=010, out equals data2
  check_sel2_route: assert property (
    @(posedge clk) (sel == 3'b010) |-> (out == data2)
  );

  // When sel=011, out equals data3
  check_sel3_route: assert property (
    @(posedge clk) (sel == 3'b011) |-> (out == data3)
  );

  // When sel=100, out equals data4
  check_sel4_route: assert property (
    @(posedge clk) (sel == 3'b100) |-> (out == data4)
  );

  // When sel=101, out equals data5
  check_sel5_route: assert property (
    @(posedge clk) (sel == 3'b101) |-> (out == data5)
  );

  // For invalid sel (110 or 111), out is zero
  check_invalid_sel_out_zero: assert property (
    @(posedge clk) (sel inside {3'b110,3'b111}) |-> (out == 4'b0000)
  );

  // Parity equals XOR of out bits
  check_parity_from_out: assert property (
    @(posedge clk) parity == (out[0] ^ out[1] ^ out[2] ^ out[3])
  );

  // For invalid sel, parity is zero (since out is zero)
  check_invalid_sel_parity_zero: assert property (
    @(posedge clk) (sel inside {3'b110,3'b111}) |-> (parity == 1'b0)
  );

endmodule