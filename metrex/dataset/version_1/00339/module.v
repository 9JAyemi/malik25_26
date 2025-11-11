
module lcd_controller(
  input clk,
  input rst,
  input i_enable,
  input i_cmd_mode,
  input i_cmd_write_stb,
  input i_cmd_read_stb,
  input [7:0] i_cmd_data,
  input [7:0] i_data,
  output reg [7:0] o_cmd_data,
  output reg [7:0] o_data,
  output reg o_cmd_finished,
  output reg o_write_n,
  output reg o_read_n,
  output reg o_cs_n,
  output reg o_reset_n,
  output reg o_data_out_en,
  output reg o_register_data_sel
);

  reg [7:0] cmd_reg;
  reg [7:0] data_reg;
  reg cmd_finished;
  reg write_n;
  reg read_n;
  reg cs_n;
  reg reset_n;
  reg data_out_en;
  reg register_data_sel;

  always @(posedge clk) begin
    if (rst) begin
      cmd_reg <= 8'h00;
      data_reg <= 8'h00;
      cmd_finished <= 1'b0;
      write_n <= 1'b0;
      read_n <= 1'b0;
      cs_n <= 1'b0;
      reset_n <= 1'b0;
      data_out_en <= 1'b0;
      register_data_sel <= 1'b0;
    end else begin
      if (i_enable) begin
        if (i_cmd_mode) begin
          if (i_cmd_write_stb) begin
            cmd_reg <= i_cmd_data;
            cmd_finished <= 1'b1;
          end else if (i_cmd_read_stb) begin
            case (i_cmd_data)
              8'h00: o_cmd_data <= 8'h00;
              8'h01: o_cmd_data <= 8'h01;
              8'h02: o_cmd_data <= 8'h02;
              8'h03: o_cmd_data <= 8'h03;
              8'h04: o_cmd_data <= 8'h04;
              8'h05: o_cmd_data <= 8'h05;
              8'h06: o_cmd_data <= 8'h06;
              8'h07: o_cmd_data <= 8'h07;
              8'h08: o_cmd_data <= 8'h08;
              8'h09: o_cmd_data <= 8'h09;
              8'h0A: o_cmd_data <= 8'h0A;
              8'h0B: o_cmd_data <= 8'h0B;
              8'h0C: o_cmd_data <= 8'h0C;
              8'h0D: o_cmd_data <= 8'h0D;
              8'h0E: o_cmd_data <= 8'h0E;
              8'h0F: o_cmd_data <= 8'h0F;
              default: o_cmd_data <= 8'h00;
            endcase
            cmd_finished <= 1'b1;
          end
        end else begin
          if (write_n) begin
            data_reg <= i_data;
            write_n <= 1'b0;
          end else if (read_n) begin
            o_data <= data_reg;
            read_n <= 1'b0;
          end
        end
      end
    end

    if (i_cmd_mode) begin
      write_n <= ~i_cmd_write_stb;
      read_n <= ~i_cmd_read_stb;
    end else begin
      write_n <= ~i_cmd_write_stb;
      read_n <= ~i_cmd_read_stb;
    end

    cs_n <= 1'b1;
    reset_n <= 1'b1;
    data_out_en <= 1'b1;
    register_data_sel <= i_cmd_mode;

    o_cmd_finished <= cmd_finished;
    o_write_n <= write_n;
    o_read_n <= read_n;
    o_cs_n <= cs_n;
    o_reset_n <= reset_n;
    o_data_out_en <= data_out_en;
    o_register_data_sel <= register_data_sel;
  end

endmodule