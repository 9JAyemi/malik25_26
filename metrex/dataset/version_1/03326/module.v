
module fifo(clk, rst, en, mode, din, we, dout, re, status, full, empty);

parameter DEPTH = 16;
parameter WIDTH = 32;

input clk, rst, en, we, re;
input [1:0] mode;
input [WIDTH-1:0] din;
output [WIDTH-1:0] dout;
output [1:0] status;
output full, empty;

reg [WIDTH-1:0] mem [0:DEPTH-1];
reg [4:0] wp, rp;
reg [1:0] status_reg;
reg [WIDTH-1:0] dout_reg;
reg empty_reg;

assign full = (wp == rp) && !empty_reg;
assign empty = (wp == rp) && empty_reg;

// write pointer logic
always @(posedge clk) begin
    if (rst) begin
        wp <= 0;
    end
    else if (en && we && !full) begin
        wp <= wp + 1;
    end
end

// read pointer logic
always @(posedge clk) begin
    if (rst) begin
        rp <= 0;
    end
    else if (en && re && !empty) begin
        rp <= rp + 1;
    end
end

// status logic
always @(posedge clk) begin
    if (rst) begin
        status_reg <= 2'b00;
    end
    else begin
        if (full) begin
            status_reg <= 2'b10;
        end
        else if (empty) begin
            status_reg <= 2'b00;
        end
        else begin
            status_reg <= 2'b01;
        end
    end
end

// empty logic
always @(posedge clk) begin
    if (rst) begin
        empty_reg <= 1'b1;
    end
    else if (en && we && !full) begin
        empty_reg <= 1'b0;
    end
    else if (en && re && empty) begin
        empty_reg <= 1'b1;
    end
end

// data output logic
always @(posedge clk) begin
    if (rst) begin
        dout_reg <= 0;
    end
    else if (en && re && !empty) begin
        case (mode)
            2'b00: dout_reg <= {16'h0, mem[rp][15:0]};
            2'b01: dout_reg <= {mem[rp][17:0], 2'h0};
            2'b10: dout_reg <= mem[rp];
            default: dout_reg <= 0;
        endcase
    end
end

// write data logic
always @(posedge clk) begin
    if (rst) begin
        mem[0] <= 0;
    end
    else if (en && we && !full) begin
        mem[wp] <= din;
    end
end

assign dout = dout_reg;
assign status = status_reg;

endmodule
