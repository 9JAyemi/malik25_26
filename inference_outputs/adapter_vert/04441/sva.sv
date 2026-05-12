property ResetSynceotid; @(posedge clk) (reset) |-> (estado_atual == IDLE) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (infrared) |-> (led) ;endproperty 
 
 property ValidTriggereotid; @(posedge clk) (infrared) &&  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  ) |->  (  (count)  == (count + 1)  ) ;endproperty 
 
 property ValidTriggereotid; @(posedge clk) (infrared) &&  (  (estado_atual == IDLE)  ) &&  (  (count)  != 130  ) |->  (  (estado_prox)  == (PRESS)  ) ;endproperty 
 
 property ValidTriggereotid; @(posedge clk) (infrared) &&  (  (estado_atual == IDLE)  ) &&  (  (count)  == 130  ) &&  (  (infrared) == 1 ) |->  (  (estado_prox)  == (BOT14)  ) ;endproperty 
 
 property ValidTriggereotid; @(posedge clk) (infrared) &&  (  (estado_atual == IDLE)  ) &&  (  (count)  == 130  ) &&  (  (infrared) != 1 ) |->  (  (estado_prox)  == (BOT23)  ) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  != 190  ) |->  (  (botao_1)  == 0  &&  (botao_2)  == 0  &&  (botao_3)  == 0  &&  (botao_4)  == 1  ) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  == 190  ) &&  (  (infrared) == 1 ) |->  (  (botao_1)  == 1  &&  (botao_2)  == 0  &&  (botao_3)  == 0  &&  (botao_4)  == 0  ) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  == 190  ) &&  (  (infrared) != 1 ) |->  (  (botao_1)  == 0  &&  (botao_2)  == 1  &&  (botao_3)  == 0  &&  (botao_4)  == 0  ) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  != 170  ) |->  (  (botao_1)  == 0  &&  (botao_2)  == 0  &&  (botao_3)  == 0  &&  (botao_4)  == 0  ) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  == 170  ) &&  (  (infrared) == 1 ) |->  (  (botao_1)  == 0  &&  (botao_2)  == 0  &&  (botao_3)  == 1  &&  (botao_4)  == 0  ) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  == 170  ) &&  (  (infrared) != 1 ) |->  (  (botao_1)  == 0  &&  (botao_2)  == 0  &&  (botao_3)  == 0  &&  (botao_4)  == 1  ) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  != 130  ) |->  (  (botao_1)  == 1  &&  (botao_2)  == 0  &&  (botao_3)  == 0  &&  (botao_4)  == 0  ) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  == 130  ) &&  (  (infrared) == 1 ) |->  (  (botao_1)  == 0  &&  (botao_2)  == 0  &&  (botao_3)  == 0  &&  (botao_4)  == 0  ) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  == 130  ) &&  (  (infrared) != 1 ) |->  (  (botao_1)  == 0  &&  (botao_2)  == 0  &&  (botao_3)  == 0  &&  (botao_4)  == 0  ) ;endproperty 
 
 