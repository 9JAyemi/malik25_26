
module bin_to_gray #(
    parameter n = 4
    )(
    input [n-1:0] bin,
    output [n-1:0] gray
    );

    wire [n-1:0] temp;
    assign temp = {bin[n-1], bin[n-1:1] ^ bin[n-2:0]};

    assign gray = temp;
    
endmodule