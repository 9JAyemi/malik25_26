
module axi_timer
    #(parameter WIDTH = 32, parameter TICK_RATE = 1)
    (input clk, rst, enable, load,
     input [WIDTH-1:0] value,
     output [WIDTH-1:0] timer,
     output reg done);

    reg [WIDTH-1:0] load_value;
    reg [WIDTH-1:0] count;

    always @(posedge clk) begin
        if (rst) begin
            count <= 0;
            done <= 0;
        end else if (enable) begin
            if (load) begin
                load_value <= value;
                count <= load_value;
                done <= 0;
            end else if (count > 0) begin
                count <= count - 1;
                done <= 0;
            end else begin
                count <= load_value;
                done <= 1;
            end
        end else begin
            done <= 0;
        end
    end

    assign timer = count;

endmodule