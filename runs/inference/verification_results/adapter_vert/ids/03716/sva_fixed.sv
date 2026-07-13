module limbus_cpu_cpu_nios2_oci_dtrace_sva (
    input logic atm,
    input logic clk,
    input logic cpu_d_address,
    input logic cpu_d_read,
    input logic cpu_d_readdata,
    input logic cpu_d_wait,
    input logic cpu_d_write,
    input logic cpu_d_writedata,
    input logic dtm,
    input logic jrst_n
);

property ResetSynceotid; @(posedge clk) (jrst_n) |-> (atm == 0) && (dtm == 0) ;endproperty
assert property (ResetSynceotid);

property ReadSynceotid; @(posedge clk) (jrst_n) && (  (cpu_d_read) && !(cpu_d_write)  && !(cpu_d_wait)  ) |-> (atm == cpu_d_address) && (dtm == cpu_d_readdata) ;endproperty
assert property (ReadSynceotid);

property WriteSynceotid; @(posedge clk) (jrst_n) && (  !(cpu_d_read) &&  (cpu_d_write)  && !(cpu_d_wait)  ) |-> (atm == cpu_d_address) && (dtm == cpu_d_writedata) ;endproperty
assert property (WriteSynceotid);

property WaitSynceotid; @(posedge clk) (jrst_n) && (  !(cpu_d_read) && !(cpu_d_write)  &&  (cpu_d_wait)  ) |-> (atm == 0) && (dtm == 0) ;endproperty
assert property (WaitSynceotid);

property DataSynceotid; @(posedge clk) (jrst_n) |-> (  (cpu_d_read) && !(cpu_d_write)  && !(cpu_d_wait)  ) || (  !(cpu_d_read) &&  (cpu_d_write)  && !(cpu_d_wait)  ) || (  !(cpu_d_read) && !(cpu_d_write)  &&  (cpu_d_wait)  ) ;endproperty
assert property (DataSynceotid);

endmodule