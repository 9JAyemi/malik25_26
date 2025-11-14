// SVA checker for bcd_converter
module bcd_converter_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [3:0]  data_in,
  input  logic [7:0]  bcd_out
);

  function automatic logic [7:0] exp_bcd(input logic [3:0] d);
    case (d)
      4'h0: exp_bcd = 8'b00000001;
      4'h1: exp_bcd = 8'b00000010;
      4'h2: exp_bcd = 8'b00000100;
      4'h3: exp_bcd = 8'b00000110;
      4'h4: exp_bcd = 8'b00001000;
      4'h5: exp_bcd = 8'b00001001;
      4'h6: exp_bcd = 8'b00001100;
      4'h7: exp_bcd = 8'b00001110;
      4'h8: exp_bcd = 8'b00010000;
      4'h9: exp_bcd = 8'b00010001;
      default: exp_bcd = 8'b00000000;
    endcase
  endfunction

  // Correct mapping for all inputs (incl. default)
  a_map: assert property (@(posedge clk) disable iff (!rst_n)
    !$isunknown(data_in) |-> (bcd_out == exp_bcd(data_in))
  );

  // Default behavior for invalid inputs 10..15
  a_default_invalid: assert property (@(posedge clk) disable iff (!rst_n)
    (data_in inside {[4'd10:4'd15]}) |-> (bcd_out == 8'h00)
  );

  // No X/Z propagation to output when input is known
  a_no_x_out: assert property (@(posedge clk) disable iff (!rst_n)
    !$isunknown(data_in) |-> !$isunknown(bcd_out)
  );

  // Purely combinational behavior (no unintended state/latch)
  a_pure_comb: assert property (@(posedge clk) disable iff (!rst_n)
    $stable(data_in) |-> $stable(bcd_out)
  );

  // Upper bits never used
  a_upper_zero: assert property (@(posedge clk) disable iff (!rst_n)
    bcd_out[7:5] == 3'b000
  );

  // For valid digits, different inputs yield different outputs
  a_injective_valid: assert property (@(posedge clk) disable iff (!rst_n)
    (data_in inside {[4'd0:4'd9]}) && $past(data_in inside {[4'd0:4'd9]}) &&
    (data_in != $past(data_in)) |-> (bcd_out != $past(bcd_out))
  );

  // Functional coverage: hit each valid input and an invalid input
  cover_0:  cover property (@(posedge clk) data_in == 4'd0);
  cover_1:  cover property (@(posedge clk) data_in == 4'd1);
  cover_2:  cover property (@(posedge clk) data_in == 4'd2);
  cover_3:  cover property (@(posedge clk) data_in == 4'd3);
  cover_4:  cover property (@(posedge clk) data_in == 4'd4);
  cover_5:  cover property (@(posedge clk) data_in == 4'd5);
  cover_6:  cover property (@(posedge clk) data_in == 4'd6);
  cover_7:  cover property (@(posedge clk) data_in == 4'd7);
  cover_8:  cover property (@(posedge clk) data_in == 4'd8);
  cover_9:  cover property (@(posedge clk) data_in == 4'd9);
  cover_inv: cover property (@(posedge clk) data_in inside {[4'd10:4'd15]});

endmodule

// Bind (provide clk/rst_n from the testbench scope)
bind bcd_converter bcd_converter_sva u_bcd_converter_sva (
  .clk   (clk),
  .rst_n (rst_n),
  .data_in (data_in),
  .bcd_out (bcd_out)
);