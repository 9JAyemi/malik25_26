// LAB 4 : counter_property.sv

// -------------------------------------------------
// CHECK #1. Check that when 'rst_' is asserted (==0)
//           data_out == 8'b0
// -------------------------------------------------
`ifdef check1
property counter_reset;
  @(posedge clk) disable iff (rst_) !rst_ |=> (data_out == 8'b0);
endproperty

counter_reset_check: assert property(counter_reset)
  else $display($stime, "\t\tCOUNTER RESET CHECK FAIL:: rst_=%b data_out=%0d \n",
                rst_, data_out);
`endif


// -------------------------------------------------
// CHECK #2. Check that if ld_cnt_ is deasserted (==1)
//           and count_enb is not enabled (==0)
//           then data_out HOLDS its previous value.
//           Disable this property 'iff (!rst_)'
// -------------------------------------------------
`ifdef check2
property counter_hold;
  @(posedge clk) disable iff (!rst_)
    (ld_cnt_ & !count_enb) |=> data_out === $past(data_out);
endproperty

counter_hold_check: assert property(counter_hold)
  else $display($stime, "\t\tCOUNTER HOLD CHECK FAIL:: counter HOLD \n");
`endif


// -------------------------------------------------
// CHECK #3. Check that if ld_cnt_ is deasserted (==1)
//           and count_enb is enabled (==1), then:
//           - if updn_cnt==1 the count goes UP
//           - if updn_cnt==0 the count goes DOWN
// -------------------------------------------------
`ifdef check3
property counter_count;
  @(posedge clk) disable iff (!rst_)
    (ld_cnt_ & count_enb) |-> 
      if (updn_cnt) ##1 (data_out-8'h01) == $past(data_out)
      else           ##1 (data_out+8'h01) == $past(data_out);
endproperty

counter_count_check: assert property(counter_count)
  else $display($stime, "\t\tCOUNTER COUNT CHECK FAIL:: UPDOWN COUNT using $past \n");
`endif


// -------------------------------------------------
// Alternate way of writing assertion for CHECK #3
// Check for count using local variable
// -------------------------------------------------
/*
`ifdef check3
property counter_count_local;
  logic [7:0] local_data;
  @(posedge clk) disable iff (!rst_)
    (ld_cnt_ & count_enb, local_data = data_out) |-> 
      if (updn_cnt) ##1 (data_out == (local_data+8'h01))
      else           ##1 (data_out == (local_data-8'h01));
endproperty

counter_count_check: assert property(counter_count)
  else $display($stime, "\t\tCOUNTER COUNT CHECK FAIL:: UPDOWN COUNT using $past \n");
`endif
*/
