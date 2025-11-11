
module parallel_port(
  input clk_i, rst_i, readstrobe_i, writestrobe_i,
  input [1:0] address_i,
  input [7:0] data_i,
  input [31:0] parport_i,
  output [31:0] parport_o,
  output [7:0] data_o,
  output parport_readstrobe_o,
  output parport_writestrobe_o
);

  reg [23:0] inputreg_r;
  reg [23:0] outputreg_r;
  reg [7:0] data_o;
  reg parport_readstrobe_o;
  reg parport_writestrobe_o;

  assign parport_o = parport_i;

  always @(*) begin
    data_o = parport_i[7:0];
    case(address_i)
      2'b01: data_o = inputreg_r[7:0];
      2'b10: data_o = inputreg_r[15:8];
      2'b11: data_o = inputreg_r[23:16];
    endcase

    parport_readstrobe_o = 0;
    if((address_i == 2'b00) && readstrobe_i) begin
      parport_readstrobe_o = 1;
    end
  end

  always @(posedge clk_i) begin
    parport_writestrobe_o <= 0;
    if(rst_i) begin
      outputreg_r <= 0;
    end else if(writestrobe_i) begin
      case(address_i)
        2'b00: outputreg_r[7:0] <= data_i;
        2'b01: outputreg_r[15:8] <= data_i;
        2'b10: outputreg_r[23:16] <= data_i;
        2'b11: begin
          parport_writestrobe_o <= 1;
        end
      endcase
    end else if(readstrobe_i) begin
      if(address_i == 2'b00) begin
        inputreg_r <= parport_i[31:8];
      end
    end
  end

endmodule