module accu(
    input               clk         ,   
    input               rst_n       ,
    input       [7:0]   data_in     ,
    input               control     ,
    input               ready_b     ,
 
    output              ready_a     ,
    output  reg         valid_b     ,
    output  reg [7:0]   data_out
);

reg [7:0] accumulator;
reg [2:0] counter;

always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
        accumulator <= 8'b0;
        counter <= 3'b0;
        valid_b <= 1'b0;
    end
    else begin
        if (control) begin
            accumulator <= accumulator ^ data_in;
            counter <= counter + 1;
            if (counter == 3'b111) begin
                data_out <= accumulator;
                accumulator <= 8'b0;
                counter <= 3'b0;
                valid_b <= 1'b1;
            end
            else begin
                valid_b <= 1'b0;
            end
        end
        else begin
            valid_b <= 1'b0;
        end
    end
end

assign ready_a = ~ready_b;

endmodule