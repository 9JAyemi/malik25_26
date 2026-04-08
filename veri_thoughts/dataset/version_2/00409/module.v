
`ifndef _timer_ `define _timer_


module timer
  #(parameter
    TIMEOUT = 100)
   (input       clk,
    input       rst,

    input       up_req,
    output      up_grant,
    input       up_ack,

    output      down_req,
    input       down_grant,
    output      down_ack
);


    

`ifdef VERBOSE
    initial $display("Bus timer with timeout %d", TIMEOUT);
`endif


    

    wire        timeout;
    reg  [31:0] counter;


    

    assign up_grant = down_grant;

    assign down_ack = up_ack;

    assign timeout = (TIMEOUT == counter);

    assign down_req = up_req & ~timeout;


    always @(posedge clk)
        if (rst) counter <= 'b0;
        else begin
            counter <= 'b0;

            if (down_grant & ~timeout) begin
                counter <= counter + 1'b1;
            end
        end


endmodule

`endif 