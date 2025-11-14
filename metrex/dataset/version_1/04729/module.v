module oneshot_2clk
  (input clk_in,
   input in,
   input clk_out,
   output reg out);

   reg 	  del_in = 0;
   reg 	  sendit = 0, gotit = 0;
   reg 	  sendit_d = 0, gotit_d = 0;
   
   always @(posedge clk_in) del_in <= in;

   always @(posedge clk_in)
     if(in & ~del_in)  sendit <= 1;
     else if(gotit)
       sendit <= 0;

   always @(posedge clk_out) sendit_d <= sendit;
   always @(posedge clk_out) out <= sendit_d;

   always @(posedge clk_in) gotit_d <= out;
   always @(posedge clk_in) gotit <= gotit_d;

endmodule 