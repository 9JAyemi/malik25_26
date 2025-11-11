

module jt12_single_acc #(parameter 
        win=14, wout=16 )(
    input                 clk,
    input                 clk_en ,
    input [win-1:0]       op_result,
    input                 sum_en,
    input                 zero,
    output reg [wout-1:0] snd
);

reg signed [wout-1:0] next, acc, current;
reg overflow;

wire [wout-1:0] plus_inf  = { 1'b0, {(wout-1){1'b1}} }; wire [wout-1:0] minus_inf = { 1'b1, {(wout-1){1'b0}} }; always @(*) begin
    current = sum_en ? { {(wout-win){op_result[win-1]}}, op_result } : {wout{1'b0}};
    next = zero ? current : current + acc;
    overflow = !zero && 
        (current[wout-1] == acc[wout-1]) && 
        (acc[wout-1]!=next[wout-1]);
end

always @(posedge clk) if( clk_en ) begin
    acc <= overflow ? (acc[wout-1] ? minus_inf : plus_inf) : next;
    if(zero) snd <= acc;
end

endmodule // jt12_single_acc