
import {
  Box, ChakraProvider,
  theme
} from "@chakra-ui/react";
import * as React from "react";
import Dashboard from './pages/Dashboard';


function Debug() {
  return <></>;
}


export default function App() {
  // return <Debug />;
  return (
    <ChakraProvider theme={theme}>
      <Box textAlign="left" fontSize="m" minH="100vh" p={2}>
        <Dashboard />
      </Box>
    </ChakraProvider >
  );
}