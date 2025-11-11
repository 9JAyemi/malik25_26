// SVA for two_bit_output
// Bind this to the DUT to check/cover functionality

module two_bit_output_sva(input logic clk,
                          input logic [3:0] b,
                          input logic [1:0] so);

  default clocking cb @(posedge clk); endclocking

  // Functional correctness: complete and mutually exclusive mapping
  property p_func_map;
    ((b inside {4'd0,4'd1,4'd2,4'd8,4'd9,4'd10,4'd11,4'd12,4'd13,4'd14,4'd15}) && so == 2'b00) ||
    ((b inside {4'd3,4'd4}) && so == 2'b01) ||
    ((b inside {4'd5,4'd6}) && so == 2'b10) ||
    ((b == 4'd7) && so == 2'b11);
  endproperty
  assert property (p_func_map);

  // Output must never be X/Z on sampling edge
  assert property (!$isunknown(so));

  // Functional coverage: hit all 16 input values with expected output
  function automatic logic [1:0] expected(input logic [3:0] v);
    case (v)
      4'd0, 4'd1, 4'd2: expected = 2'b00;
      4'd3, 4'd4:       expected = 2'b01;
      4'd5, 4'd6:       expected = 2'b10;
      4'd7:             expected = 2'b11;
      default:          expected = 2'b00;
    endcase
  endfunction

  genvar gi;
  generate
    for (gi = 0; gi < 16; gi++) begin : COV_ALL_B
      localparam logic [3:0] I = gi[3:0];
      cover property (b == I && so == expected(I));
    end
  endgenerate

endmodule

bind two_bit_output two_bit_output_sva sva_inst(.clk(clk), .b(b), .so(so));