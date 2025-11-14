
module decoder_74138_dataflow(
    input [2:0] x,
    input g1,g2a_n,g2b_n,
    output [7:0] y
    );
    assign y[0] = g2a_n|g2b_n|(~g1)|x[0]|x[1]|x[2];
    assign y[1] = g2a_n|g2b_n|(~g1)|x[0]|x[1]|(~x[2]);
    assign y[2] = g2a_n|g2b_n|(~g1)|x[0]|(~x[1])|x[2];
    assign y[3] = g2a_n|g2b_n|(~g1)|x[0]|(~x[1])|(~x[2]);
    assign  y[4] = g2a_n|g2b_n|(~g1)|(~x[0])|x[1]|x[2];
    assign y[5] = g2a_n|g2b_n|(~g1)|(~x[0])|x[1]|(~x[2]);
    assign y[6] = g2a_n|g2b_n|(~g1)|(~x[0])|(~x[1])|x[2];
    assign y[7] = g2a_n|g2b_n|(~g1)|(~x[0])|(~x[1])|(~x[2]);
   
    
endmodule
