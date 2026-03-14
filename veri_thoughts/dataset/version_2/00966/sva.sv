module shift_mux_array_sva
  #(parameter int SWR = 26, parameter int LEVEL = 5)
  (
    input  logic                   clk,
    input  logic [SWR-1:0]         Data_i,
    input  logic                   select_i,
    input  logic                   bit_shift_i,
    input  logic [SWR-1:0]         Data_o
  );

  // Replicate RTL constants
  localparam int lvl = 2**(LEVEL);
  localparam int x   = SWR - 1;

  // When select_i=0, output passes through input vector.
  check_passthrough_when_select0: assert property (
    @(posedge clk) disable iff (1'b0) (!select_i) |=> (Data_o == Data_i)
  );

  genvar j;
  generate
    for (j = 0; j <= SWR-1; j = j + 1) begin : gen_bit_checks
      if ((lvl + j) > x) begin : fill_region
        // With select_i=1 and index out-of-range, Data_o[j] equals bit_shift_i.
        check_sel1_fill_bit: assert property (
          @(posedge clk) disable iff (1'b0) (select_i) |=> (Data_o[j] == bit_shift_i)
        );
      end else begin : forward_region
        // With select_i=1 and index in-range, Data_o[j] maps to Data_i[lvl+j].
        check_sel1_forward_bit: assert property (
          @(posedge clk) disable iff (1'b0) (select_i) |=> (Data_o[j] == Data_i[lvl + j])
        );
      end
    end
  endgenerate

endmodule