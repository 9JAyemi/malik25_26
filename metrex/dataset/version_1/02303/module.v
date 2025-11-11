
module barrel_shifter (
    input [7:0] data_in,
    input [1:0] shift_amt,
    input shift_dir,
    input enable,
    output [7:0] data_out
);

reg [7:0] data_out_int;

always @(*) begin
    if (enable) begin
        if (shift_dir) begin
            data_out_int = data_in << shift_amt;
        end else begin
            data_out_int = data_in >> shift_amt;
        end
    end else begin
        data_out_int = data_in;
    end
end

assign data_out = data_out_int;

endmodule

module up_down_counter (
    input clk,
    input rst,
    input load,
    input up_down,
    input [7:0] data_in,
    output [7:0] data_out
);

reg [7:0] count;

always @(posedge clk) begin
    if (rst) begin
        count <= 0;
    end else if (load) begin
        count <= data_in;
    end else begin
        if (up_down) begin
            count <= count + 1;
        end else begin
            count <= count - 1;
        end
    end
end

assign data_out = count;

endmodule

module bitwise_and (
    input [7:0] data_in1,
    input [7:0] data_in2,
    output [7:0] data_out
);

assign data_out = data_in1 & data_in2;

endmodule
