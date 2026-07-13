module sync_up_counter #(parameter WIDTH=4)
                       (input wire clk, input wire rst, input wire load,
                        input wire[WIDTH-1:0] data_in, output reg[WIDTH-1:0] count);

    always @(posedge clk) begin
        if (rst) begin
            count <= 0;
        end else if (load) begin
            count <= data_in;
        end else begin
            count <= count + 1;
        end
    end

endmodule