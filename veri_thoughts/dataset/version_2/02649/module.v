module servo
#(
    parameter WIDTH = 16, parameter NUM = 1     ) (
    input clk50Mhz,                   input rst,                        input [(WIDTH*NUM)-1:0] posArray, output reg [NUM-1:0] pwm          );

wire [WIDTH-1:0] posArrayInternal[NUM-1:0];

reg [19:0] counter;

integer i;
genvar j;

generate
begin
    for (j=0; j<NUM; j=j+1) begin
        assign posArrayInternal[j] = posArray[(WIDTH*(j+1)-1):(WIDTH*j)];
    end
end
endgenerate

always @(posedge clk50Mhz) begin
    if (rst) begin
        counter <= 'd0;
        pwm <= 'b0;
    end else begin
        counter <= counter + 1;
        for (i=0; i<NUM; i=i+1) begin
            if (((posArrayInternal[i] << (16-WIDTH)) + 42232) > counter)
                pwm[i] <= 1'b1;
            else
                pwm[i] <= 1'b0;
        end
    end
end

endmodule
