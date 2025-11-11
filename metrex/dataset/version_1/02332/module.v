module modbus (
  input clk,
  input rst,
  input en,
  input [7:0] addr,
  input [7:0] data_in,
  output [7:0] data_out,
  output done
);

parameter is_master = 1; // set to 1 for master and 0 for slave

reg [7:0] reg_addr;
reg [7:0] reg_data;
reg [7:0] request;
reg [7:0] response;
reg [2:0] state;
reg done;

assign data_out = response;

always @(posedge clk) begin
  if (rst) begin
    state <= 0;
    done <= 0;
  end else if (en) begin
    case (state)
      0: begin // idle
        if (is_master) begin
          state <= 1;
          request <= {addr, 0, reg_addr, reg_data}; // read holding register
        end else begin
          if (addr == request[0]) begin
            case (request[1])
              3: begin // read holding register
                state <= 1;
              end
              default: begin
                state <= 0;
              end
            endcase
          end
        end
      end
      1: begin // send request
        if (is_master) begin
          state <= 2;
        end else begin
          response <= {addr, request[1], reg_data};
          state <= 0;
          done <= 1;
        end
      end
      2: begin // wait for response
        if (is_master) begin
          state <= 3;
        end else begin
          state <= 0;
        end
      end
      3: begin // receive response
        if (is_master) begin
          response <= data_in;
          state <= 0;
          done <= 1;
        end else begin
          reg_data <= data_in;
          response <= {addr, request[1], reg_data};
          state <= 0;
          done <= 1;
        end
      end
      default: begin
        state <= 0;
      end
    endcase
  end
end

endmodule