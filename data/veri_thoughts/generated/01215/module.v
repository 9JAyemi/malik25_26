
module nova_io_pio_dummy (
  input wire pclk,
  input wire bs_rst,
  input wire bs_stb,
  input wire bs_we,
  input wire [7:0] bs_adr,
  input wire [15:0] bs_din,
  output wire [15:0] bs_dout
);

  parameter device_addr = 6'b000000;

  reg r_DONE;
  reg r_BUSY;

  assign bs_dout = {r_BUSY, r_DONE, 14'h0000};

  always @(posedge pclk or negedge bs_rst) begin
    if (!bs_rst) begin
      r_DONE <= 1'b1;
      r_BUSY <= 1'b0;
    end else begin
      if (bs_stb & (bs_adr[5:0] == device_addr)) begin
        case (bs_we)
          1'b1: begin
            case (bs_adr[7:6])
              2'b00: begin
                case (bs_din[15:14])
                  2'b01: begin
                    r_DONE <= 1'b0;
                    r_BUSY <= 1'b1;
                  end
                  2'b10: begin
                    r_DONE <= 1'b0;
                    r_BUSY <= 1'b0;
                  end
                  2'b11: begin
                    // Pulse
                  end
                endcase // case (bs_din[15:14])
              end // case (bs_adr[7:6] == 2'b00)
              2'b01: begin
                 `ifdef SIMULATION
                   `ifndef YOSYS
                    $display("%m DIA");
                   `endif
                 `endif
              end
              2'b10: begin
                 `ifdef SIMULATION
                   `ifndef YOSYS
                    $display("%m DIB");
                   `endif
                 `endif
              end
              2'b11: begin
                 `ifdef SIMULATION
                   `ifndef YOSYS
                    $display("%m DIC");
                   `endif
                 `endif
              end
            endcase // case (bs_adr[7:6])
          end // case (bs_we == 1'b1)
          1'b0: begin
            case (bs_adr[7:6])
              2'b00: ;
              2'b01: begin
                 `ifdef SIMULATION
                   `ifndef YOSYS
                    $display("%m DIA");
                   `endif
                 `endif
              end
              2'b10: begin
                 `ifdef SIMULATION
                   `ifndef YOSYS
                    $display("%m DIB");
                   `endif
                 `endif
              end
              2'b11: begin
                 `ifdef SIMULATION
                   `ifndef YOSYS
                    $display("%m DIC");
                   `endif
                 `endif
              end
            endcase // case (bs_adr[7:6])
          end // case (bs_we == 1'b0)
        endcase // case (bs_we)
      end // if (bs_stb & (bs_adr[5:0] == device_addr))
    end // else (!bs_rst)
  end // always @ (posedge pclk)

endmodule