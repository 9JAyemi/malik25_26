module black_box (
  data_out,
  full_flag,
  empty_flag,
  write_en,
  read_en,
  clk,
  rst_,
  data_in
);

parameter depth = 8;
parameter width = 8;

output logic [(width - 1):0] data_out;
output logic full_flag, empty_flag;
input  logic write_en, read_en, clk, rst_;
input  logic [(width - 1):0] data_in;

logic [(width-1):0] mem [0:(depth-1)];
logic [3:0] wr_ptr, rd_ptr;
logic [3:0] count;

always @ (posedge clk or negedge rst_) begin
  if (!rst_) begin
    rd_ptr    <= 0;
    wr_ptr    <= 0;
    count     <= 0;
    `ifndef check1
      empty_flag <= 1;
    `endif
    full_flag <= 0;
  end
  else begin
    case ({write_en, read_en})
      2'b00: ; // idle

      2'b01: begin // read
        if (count > 0) begin
          rd_ptr <= rd_ptr + 1;
          count  <= count - 1;
        end
        `ifdef check2
          if (count == 0) empty_flag <= 1;
        `else
          `ifdef check5
            if (count == 1) empty_flag <= 1;
            rd_ptr <= rd_ptr + 1;
          `else
            if (count == 1) empty_flag <= 1;
          `endif
        `endif
        full_flag <= 0;
      end

      2'b10: begin // write
        if (count < depth) begin
          mem[wr_ptr] <= data_in;
          wr_ptr      <= wr_ptr + 1;
          count       <= count + 1;
        end
        `ifdef check3
          if (count > (depth - 1)) full_flag <= 1;
        `else
          `ifdef check4
            if (count >= (depth - 1)) full_flag <= 1;
            wr_ptr <= wr_ptr + 1;
          `else
            if (count >= (depth - 1)) full_flag <= 1;
          `endif
        `endif
        empty_flag <= 0;
      end

      2'b11: begin // write && read
        // If full: read only
        if (count > (depth - 1)) begin
          rd_ptr <= rd_ptr + 1;
          count  <= count - 1;
        end
        // If empty: write only
        else if (count < 1) begin
          mem[wr_ptr] <= data_in;
          wr_ptr      <= wr_ptr + 1;
          count       <= count + 1;
        end
        // Otherwise: do both
        else begin
          mem[wr_ptr] <= data_in;
          wr_ptr      <= wr_ptr + 1;
          rd_ptr      <= rd_ptr + 1;
        end
      end
    endcase
  end
end

assign data_out = mem[rd_ptr];

endmodule
