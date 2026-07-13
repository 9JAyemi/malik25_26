property ResetSynceotid; @(posedge clk) (jrst_n) |-> (atm == 0) && (dtm == 0) ;endproperty 
 
 property ReadSynceotid; @(posedge clk) (jrst_n) && (  (cpu_d_read) && !(cpu_d_write)  && !(cpu_d_wait)  ) |-> (atm == cpu_d_address) && (dtm == cpu_d_readdata) ;endproperty 
 
 property WriteSynceotid; @(posedge clk) (jrst_n) && (  !(cpu_d_read) &&  (cpu_d_write)  && !(cpu_d_wait)  ) |-> (atm == cpu_d_address) && (dtm == cpu_d_writedata) ;endproperty 
 
 property WaitSynceotid; @(posedge clk) (jrst_n) && (  !(cpu_d_read) && !(cpu_d_write)  &&  (cpu_d_wait)  ) |-> (atm == 0) && (dtm == 0) ;endproperty 
 
 property DataSynceotid; @(posedge clk) (jrst_n) |-> (  (cpu_d_read) && !(cpu_d_write)  && !(cpu_d_wait)  ) || (  !(cpu_d_read) &&  (cpu_d_write)  && !(cpu_d_wait)  ) || (  !(cpu_d_read) && !(cpu_d_write)  &&  (cpu_d_wait)  ) ;endproperty 
 